import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.AdeleRing
import FLT.NumberField.AdeleRing

/-!
# S-adele and direct limit

We define the S-adele `𝔸_{K,S} = { x ∈ 𝔸 K | x_v ∈ 𝓞_v for all v ∉ S }`,
We will proved that the Adele ring is the direct limit of S-adele

Firstly we proved the finite version: the finite Adele ring is the direct limit
of the finite S-adele

In order to proved the results of direct limit, we need to prove the following three things
- S-adele form a monotone family of subring
- their supremum is the whole finite adele ring.
- and finite adele lies in some S-adele subring.

Then we lift it to the genuine `S`-adele ring `sAdele`, a subring of the *full* adele
ring `𝔸 K`, where `S` is an arbitrary finite set of places (`S : Finset (Place K)` —
infinite places, finite places, or both). The same three facts give
`iSup_sAdele : ⨆ S, sAdele K S = ⊤`, i.e. the adele ring is the direct limit of the
`S`-adeles.

-/

open IsDedekindDomain HeightOneSpectrum


variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
variable (S : Finset (HeightOneSpectrum R))
/-- The subring of `S`-adeles inside the finite adele ring: finite adeles that are
integral at every prime outside the finite set `S`. -/
def finiteSAdele : Subring (FiniteAdeleRing R K) where
  carrier := {x | ∀ v ∉ S, x v ∈ v.adicCompletionIntegers K}
  mul_mem' hx hy v hv := mul_mem (hx v hv) (hy v hv)
  one_mem' _ _ := one_mem _
  add_mem' hx hy v hv := add_mem (hx v hv) (hy v hv)
  zero_mem' _ _ := zero_mem _
  neg_mem' hx v hv := neg_mem (hx v hv)

/-- we can define a partially order forall finset of prime ideal, and we can assign each finset to
a finite S adele. -/
lemma finiteSAdele_mono : Monotone (finiteSAdele R K) := by
  intro S T hST x hx v hv
  apply hx
  intro h
  have h_in_T : v ∈ T := hST h
  exact hv h_in_T


/-- The family of `S`-adele subrings is directed: any two are contained in the
`S`-adeles for their union. -/
lemma finiteSAdele_directed : Directed (· ≤ ·) (finiteSAdele R K) := by
  classical
  exact fun S T => ⟨S ∪ T, finiteSAdele_mono R K Finset.subset_union_left,
  finiteSAdele_mono R K Finset.subset_union_right⟩

/-- **The finite adele ring is the direct limit of the `S`-adeles.**
The supremum of the (directed) family of `S`-adele subrings is the whole finite
adele ring. -/
theorem iSup_finiteSAdele : ⨆ S, finiteSAdele R K S = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x hx
  rw [Subring.mem_iSup_of_directed (finiteSAdele_directed R K)]
  -- `x` is integral outside the finite "bad set" of primes where it is non-integral.
  have hbad : {v : HeightOneSpectrum R | x v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp x.2
  refine ⟨hbad.toFinset, fun v hv => ?_⟩
  by_contra hmem
  exact hv (hbad.mem_toFinset.mpr hmem)

variable {R K}

/-- Every finite adele lies in some `S`-adele subring (membership form of
`iSup_finiteSAdele`). -/
theorem mem_iSup_finiteSAdele (x : FiniteAdeleRing R K) :
    ∃ S, x ∈ finiteSAdele R K S := by
  have := (iSup_finiteSAdele R K).ge (Subring.mem_top x)
  rwa [Subring.mem_iSup_of_directed (finiteSAdele_directed R K)] at this

/-! ### The full `S`-adele ring (`S` a finite set of places)

The genuine `S`-adele ring sits inside the **full** adele ring `𝔸 K`, not just the
finite adele ring, and `S` is an arbitrary **finite set of places** — infinite,
finite, or both (`S : Finset (Place K)`). Concretely
`𝔸_{K,S} = ∏_{v ∈ S} K_v × ∏_{v ∉ S} 𝓞_v ⊆ 𝔸 K`.
At an infinite place there is no integrality condition (the local ring is all of
`K_v`), so the infinite places of `S` — and indeed all infinite places — are
unrestricted regardless: only the finite places *outside* `S` constrain an adele,
and the finite part of an `S`-adele is a `finiteSAdele`. As `S` grows the union is
the whole adele ring (`iSup_sAdele`). -/

open scoped NumberField.AdeleRing
open NumberField

section
variable (K : Type*) [Field K] [NumberField K]

/-- The places of a number field `K`: the infinite places (archimedean) together
with the finite places (height-one primes of `𝓞 K`). -/
abbrev Place := InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)

/-- The **`S`-adele ring** for a finite set of places `S : Finset (Place K)`, which
may contain infinite places, finite places, or both: the adeles of the full adele
ring `𝔸 K` that are integral at every finite place outside `S`. Infinite places
impose no condition (their local field has no proper subring of integers), so only
the finite places of `S` matter. -/
def sAdele (S : Finset (Place K)) : Subring (𝔸 K) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 K), (Sum.inr v : Place K) ∉ S →
    x.2 v ∈ v.adicCompletionIntegers K}
  mul_mem' hx hy v hv := mul_mem (hx v hv) (hy v hv)
  one_mem' _ _ := one_mem _
  add_mem' hx hy v hv := add_mem (hx v hv) (hy v hv)
  zero_mem' _ _ := zero_mem _
  neg_mem' hx v hv := neg_mem (hx v hv)

variable {K}

@[simp]
lemma mem_sAdele {S : Finset (Place K)} {x : 𝔸 K} :
    x ∈ sAdele K S ↔ ∀ v : HeightOneSpectrum (𝓞 K), (Sum.inr v : Place K) ∉ S →
      x.2 v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

variable (K)

/-- The `S`-adeles grow with `S`. -/
lemma sAdele_mono : Monotone (sAdele K) :=
  fun _ _ hST _ hx v hv => hx v (fun h => hv (hST h))

/-- The family of `S`-adele subrings is directed. -/
lemma sAdele_directed : Directed (· ≤ ·) (sAdele K) := by
  classical
  exact fun S T => ⟨S ∪ T, sAdele_mono K Finset.subset_union_left,
                          sAdele_mono K Finset.subset_union_right⟩

/-- **The adele ring is the direct limit of the `S`-adeles.** The supremum of the
(directed) family of `S`-adele subrings is the whole adele ring `𝔸 K`. -/
theorem iSup_sAdele : ⨆ S, sAdele K S = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  rw [Subring.mem_iSup_of_directed (sAdele_directed K)]
  -- the finite part `x.2` is integral outside its finite "bad set" of finite places
  have hbad : {v : HeightOneSpectrum (𝓞 K) | x.2 v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp x.2.2
  -- take `S` to be that bad set, regarded as a finite set of (finite) places
  refine ⟨hbad.toFinset.image Sum.inr, fun v hv => ?_⟩
  by_contra hmem
  exact hv (Finset.mem_image_of_mem Sum.inr (hbad.mem_toFinset.mpr hmem))

variable {K}

/-- Every adele lies in some `S`-adele subring (membership form of `iSup_sAdele`). -/
theorem mem_iSup_sAdele (x : 𝔸 K) :
    ∃ S : Finset (Place K), x ∈ sAdele K S := by
  have := (iSup_sAdele K).ge (Subring.mem_top x)
  rwa [Subring.mem_iSup_of_directed (sAdele_directed K)] at this

end
