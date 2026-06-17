import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Completion
import Mathlib.NumberTheory.NumberField.FinitePlaces
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import FLT.Mathlib.Analysis.Normed.Ring.WithAbs

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

open scoped BigOperators
open Filter Topology NumberField IsDedekindDomain
/-!
### Weak approximation in Mathlib

Mathlib proves weak approximation in (`NumberField.InfinitePlace.denseRange_algebraMap_pi`,
which proved that K is dense in ∏_{v∣ ∞} (K,|·|ᵥ), it's not the completion of v
But the K with the topology induced by |·|ᵥ.

While the FLT version proved that K is dense in ∏_{p∈ S.finite ⊆ M _{∞}}Kᵥ in
`NumberField.InfinitePlace.Completion.denseRange_algebraMap_subtype_pi`).

Here we firstly prove the **general version**: any field `K` carrying finitely many pairwise
inequivalent nontrivial real absolute values embeds densely in the product
`Π i, (K, |·|ᵢ)` (`denseRange_algebraMap_pi`), and hence densely in the product of
completions `Π i, (v i).Completion` (`denseRange_algebraMap_pi_completion`).
-/

open AbsoluteValue Filter

variable {K : Type*} [Field K] {ι : Type*} [Finite ι] {v : ι → AbsoluteValue K ℝ}

theorem denseRange_algebraMap_pi
    (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j => ¬(v i).IsEquiv (v j)) :
    DenseRange <| algebraMap K ((i : ι) → WithAbs (v i)) := by
  classical
  have := Fintype.ofFinite ι
  refine Metric.denseRange_iff.mpr fun z r hr => ?_
  -- For each i pick aᵢ with 1 < vᵢ aᵢ and vⱼ aᵢ < 1 for j ≠ i.
  choose a hx using exists_one_lt_lt_one_pi_of_not_isEquiv h hv
  -- The sequence yₙ = ∑ i, 1/(1 + aᵢ⁻ⁿ) · zᵢ converges to z in every factor.
  let y := fun n : ℕ => ∑ i, (1 / (1 + (a i)⁻¹ ^ n)) * WithAbs.equiv (v i) (z i)
  have htend : atTop.Tendsto (fun n i => (WithAbs.equiv (v i)).symm (y n)) (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u => ?_
    simp_rw [← Fintype.sum_pi_single u z, y, map_sum, map_mul]
    refine tendsto_finset_sum _ fun w _ => ?_
    by_cases hw : u = w
    · -- the diagonal summand: 1/(1 + aᵤ⁻ⁿ) → 1 in (K, vᵤ)
      rw [← hw, Pi.single_apply u (z u), if_pos rfl]
      have hlt : (v u) (a u)⁻¹ < 1 := by
        simpa [← inv_pow, inv_lt_one_iff₀] using Or.inr (hx u).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one hlt).mul_const (z u)
    · -- the off-diagonal summands: 1/(1 + a_w⁻ⁿ) → 0 in (K, vᵤ) for w ≠ u
      simp only [Pi.single_apply w (z w), hw, if_false]
      have hgt : 1 < (v u) (a w)⁻¹ := by
        rw [map_inv₀]
        refine one_lt_inv_iff₀.mpr ⟨(v u).pos_iff.mpr fun ha => ?_, (hx w).2 u hw⟩
        linarith [map_zero (v w) ▸ ha ▸ (hx w).1]
      simpa using
        (tendsto_zero_iff_norm_tendsto_zero.2 <|
          (v u).tendsto_div_one_add_pow_nhds_zero hgt).mul_const
          ((WithAbs.equiv (v u)).symm _)
  let ⟨N, hN⟩ := Metric.tendsto_atTop.1 htend r hr
  exact ⟨y N, dist_comm z (algebraMap K _ (y N)) ▸ hN N le_rfl⟩

theorem denseRange_algebraMap_pi_completion
    (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j => ¬(v i).IsEquiv (v j)) :
    DenseRange <| algebraMap K ((i : ι) → (v i).Completion) := by
  -- The map factors as (Π coe) ∘ (diagonal into Π WithAbs), both with dense range.
  have hcomp : algebraMap K ((i : ι) → (v i).Completion) =
      (Pi.map fun i => ((↑) : WithAbs (v i) → (v i).Completion)) ∘
        algebraMap K ((i : ι) → WithAbs (v i)) := rfl
  rw [hcomp]
  exact DenseRange.comp
    (DenseRange.piMap fun i => UniformSpace.Completion.denseRange_coe)
    (denseRange_algebraMap_pi h hv)
    (Continuous.piMap fun i => UniformSpace.Completion.continuous_coe _)

/-- **Specialization sanity check**: the general theorem recovers weak approximation
    for any subcollection of infinite places of a number field — the statement of
    `NumberField.InfinitePlace.Completion.denseRange_algebraMap_subtype_pi` (FLT). -/
theorem denseRange_algebraMap_subtype_pi_infinitePlace
    (K : Type*) [Field K] [NumberField K] (p : InfinitePlace K → Prop) :
    DenseRange <| algebraMap K ((w : Subtype p) → w.1.Completion) :=
  denseRange_algebraMap_pi_completion
    (fun w => w.1.isNontrivial)
    (fun _ _ hne hequiv =>
      hne (Subtype.ext (NumberField.InfinitePlace.eq_iff_isEquiv.mpr hequiv)))

/-! `NumberField.FinitePlace K` and `NumberField.InfinitePlace K` are both subtypes of
`AbsoluteValue K ℝ`, so the general theorems above apply to any finite family of
places — finite or infinite — once we know:
- every finite place is a nontrivial absolute value (`finitePlace_isNontrivial`);
- distinct finite places are inequivalent (`finitePlace_eq_iff_isEquiv`);
- a finite place is never equivalent to an infinite place
  (`not_isEquiv_finitePlace_infinitePlace`).

These give weak approximation at any finite collection of places of a number field
(`denseRange_algebraMap_pi_place`, `denseRange_algebraMap_pi_completion_place`),
So we get the general version of weak approximation theorem -/


variable {K : Type*} [Field K] [NumberField K]

/-- Finite places are nontrivial absolute values: any nonzero element of the
    associated maximal ideal has absolute value < 1. -/
lemma finitePlace_isNontrivial (w : FinitePlace K) : w.1.IsNontrivial := by
  obtain ⟨x, hx_mem, hx_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot w.maximalIdeal.ne_bot
  refine ⟨(x : K), by simpa using hx_ne, ne_of_lt ?_⟩
  calc w.1 (x : K) = ‖FinitePlace.embedding w.maximalIdeal (x : K)‖ :=
        (FinitePlace.norm_embedding_eq w (x : K)).symm
    _ < 1 := (FinitePlace.norm_lt_one_iff_mem w.maximalIdeal x).mpr hx_mem

/-- Two finite places are equal iff their absolute values are equivalent.
    (Distinct primes give inequivalent absolute values: an element of one maximal
    ideal but not the other separates them.) -/
lemma finitePlace_eq_iff_isEquiv {w₁ w₂ : FinitePlace K} :
    w₁ = w₂ ↔ w₁.1.IsEquiv w₂.1 := by
  refine ⟨fun h => h ▸ .rfl, fun h => ?_⟩
  by_contra hne
  -- The maximal ideals are distinct maximal ideals, so the first is not ≤ the second.
  have h_not_le : ¬w₁.maximalIdeal.asIdeal ≤ w₂.maximalIdeal.asIdeal := by
    intro hle
    have heq : w₁.maximalIdeal.asIdeal = w₂.maximalIdeal.asIdeal :=
      (Ring.DimensionLEOne.maximalOfPrime w₁.maximalIdeal.ne_bot
        w₁.maximalIdeal.isPrime).eq_of_le
        (Ring.DimensionLEOne.maximalOfPrime w₂.maximalIdeal.ne_bot
          w₂.maximalIdeal.isPrime).ne_top hle
    exact hne ((FinitePlace.maximalIdeal_inj w₁ w₂).mp (HeightOneSpectrum.ext heq))
  obtain ⟨x, hx₁, hx₂⟩ := SetLike.not_le_iff_exists.mp h_not_le
  -- w₁ x < 1 but w₂ x = 1, contradicting equivalence.
  have h1 : w₁.1 (x : K) < 1 := by
    calc w₁.1 (x : K) = ‖FinitePlace.embedding w₁.maximalIdeal (x : K)‖ :=
          (FinitePlace.norm_embedding_eq w₁ (x : K)).symm
      _ < 1 := (FinitePlace.norm_lt_one_iff_mem w₁.maximalIdeal x).mpr hx₁
  have h2 : w₂.1 (x : K) = 1 :=
    calc w₂.1 (x : K) = ‖FinitePlace.embedding w₂.maximalIdeal (x : K)‖ :=
          (FinitePlace.norm_embedding_eq w₂ (x : K)).symm
      _ = 1 := (FinitePlace.norm_eq_one_iff_notMem w₂.maximalIdeal x).mpr hx₂
  rw [h.lt_one_iff] at h1
  exact absurd h2 (ne_of_lt h1)

/-- Finite_Places is inequivalent to infinite Places -/
lemma not_isEquiv_finitePlace_infinitePlace (w : FinitePlace K) (w' : InfinitePlace K) :
    ¬w.1.IsEquiv w'.1 := by
  intro h
  -- Bridge: w as an absolute value is the v-adic absolute value of its maximal ideal.
  have hbridge : ∀ x : K,
      w.1 x = RingOfIntegers.HeightOneSpectrum.adicAbv w.maximalIdeal x := fun x => by
    rw [show w.1 x = w x from rfl, ← FinitePlace.norm_embedding_eq, FinitePlace.norm_def]
  have h2fin : w.1 ((2 : ℕ) : K) ≤ 1 := by
    rw [hbridge]
    exact RingOfIntegers.HeightOneSpectrum.adicAbv_natCast_le_one w.maximalIdeal 2
  have h2inf : w'.1 ((2 : ℕ) : K) = 2 := by
    rw [show w'.1 ((2 : ℕ) : K) = w' ((2 : ℕ) : K) from rfl, InfinitePlace.map_natCast]
    norm_num
  have hle := h.le_one_iff.mp h2fin
  rw [h2inf] at hle
  norm_num at hle

variable (K)

/-- The underlying absolute value of a place — finite or infinite — of a
    number field. -/
def placeAbv : FinitePlace K ⊕ InfinitePlace K → AbsoluteValue K ℝ :=
  Sum.elim Subtype.val Subtype.val

lemma placeAbv_isNontrivial (P : FinitePlace K ⊕ InfinitePlace K) :
    (placeAbv K P).IsNontrivial := by
  cases P with
  | inl w => exact finitePlace_isNontrivial w
  | inr w => exact w.isNontrivial

lemma placeAbv_pairwise_not_isEquiv :
    Pairwise fun P Q => ¬(placeAbv K P).IsEquiv (placeAbv K Q) := by
  rintro (w₁ | w₁) (w₂ | w₂) hne hequiv
  · exact hne (congrArg Sum.inl (finitePlace_eq_iff_isEquiv.mpr hequiv))
  · exact not_isEquiv_finitePlace_infinitePlace w₁ w₂ hequiv
  · exact not_isEquiv_finitePlace_infinitePlace w₂ w₁ hequiv.symm
  · exact hne (congrArg Sum.inr (NumberField.InfinitePlace.eq_iff_isEquiv.mpr hequiv))

/-- **Weak approximation for all places of a number field** : K embeds densely into the product of
    `(K, |·|_P)` over any finite collection of places. -/
theorem denseRange_algebraMap_pi_place
    (p : FinitePlace K ⊕ InfinitePlace K → Prop) [Finite {P // p P}] :
    DenseRange <| algebraMap K ((P : {P // p P}) → WithAbs (placeAbv K P.1)) :=
  denseRange_algebraMap_pi (fun P => placeAbv_isNontrivial K P.1)
    ((placeAbv_pairwise_not_isEquiv K).comp_of_injective Subtype.val_injective)

/-- **Weak approximation at the places of a number field, in the completions**:
    K embeds densely into the product of completions over any finite collection
    of places, finite and infinite. -/
theorem denseRange_algebraMap_pi_completion_place
    (p : FinitePlace K ⊕ InfinitePlace K → Prop) [Finite {P // p P}] :
    DenseRange <| algebraMap K ((P : {P // p P}) → (placeAbv K P.1).Completion) :=
  denseRange_algebraMap_pi_completion (fun P => placeAbv_isNontrivial K P.1)
    ((placeAbv_pairwise_not_isEquiv K).comp_of_injective Subtype.val_injective)
