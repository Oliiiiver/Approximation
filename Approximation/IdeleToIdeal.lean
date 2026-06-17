import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.GroupTheory.QuotientGroup.Basic
import FLT.DedekindDomain.FiniteAdeleRing.LocalUnits

/-!
# The idele-to-fractional-ideal map

Let `R` be a Dedekind domain with fraction field `K`. We study the homomorphism
from the (finite) idele group to the group of invertible fractional ideals,
\[
  I_K \longrightarrow J_K, \qquad
  (x_v)_v \longmapsto \prod_v \mathfrak p_v^{\,\operatorname{ord}_v(x_v)},
\]
the product running over the finite places (nonzero primes `v`), where
`ord_v(x_v) ∈ ℤ` is the normalized additive valuation of the local component.
For an idele the exponents vanish for all but finitely many `v`, so the product is
a genuine (finite) product and lands in the invertible fractional ideals.

## Main definitions
* `ideleOrd x v` : the integer `ord_v(x_v)` for a finite idele `x`.
* `ideleToFractionalIdeal` : the group homomorphism
  `(FiniteAdeleRing R K)ˣ →* (FractionalIdeal R⁰ K)ˣ`.

## Main results
* `ideleToFractionalIdeal_apply`, `count_ideleToFractionalIdeal` : the underlying
  fractional ideal is `∏ᶠ v, v.asIdeal ^ ord_v(x_v)`, and its `v`-adic count is
  `ord_v(x_v)`.
* `mem_ker_ideleToFractionalIdeal` : the kernel consists of the ideles that are
  units of `𝓞_v` at every finite place.
* `ideleToFractionalIdeal_surjective` : the map is surjective.
* `ideleToFractionalIdeal_not_injective` : it is not injective.
-/

open IsDedekindDomain HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors

namespace IsDedekindDomain.FiniteAdeleRing

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- Each local component of a finite idele is a unit of the completion, in
particular nonzero. -/
lemma component_isUnit (x : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    IsUnit ((x : FiniteAdeleRing R K) v) :=
  ⟨⟨(x : FiniteAdeleRing R K) v, ((↑x⁻¹ : FiniteAdeleRing R K) v),
    by rw [← mul_apply, x.mul_inv, one_apply], by rw [← mul_apply, x.inv_mul, one_apply]⟩, rfl⟩

lemma component_ne_zero (x : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    (x : FiniteAdeleRing R K) v ≠ 0 :=
  (component_isUnit x v).ne_zero

lemma valued_component_ne_zero (x : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    Valued.v ((x : FiniteAdeleRing R K) v) ≠ 0 :=
  (Valuation.ne_zero_iff Valued.v).mpr (component_ne_zero x v)

/-- The normalized additive valuation `ord_v(a_v) ∈ ℤ` of the `v`-component of a
finite adele `a`, with the convention `ord_v(0) = 0`. With the Mathlib convention
`Valued.v π = ofAdd (-1)` for a uniformizer `π`, a uniformizer has `adeleOrd = 1`.

This is the **single** exponent function underlying both the idele-to-ideal map
(`ideleOrd`, the restriction to units) and the Blichfeldt–Minkowski argument
(`Approximation.Blichfeldt`, via `fractionalIdealOfExps (adeleOrd a)`). -/
noncomputable def adeleOrd (a : FiniteAdeleRing R K) (v : HeightOneSpectrum R) : ℤ :=
  if h : Valued.v (a v) = 0 then 0
  else - Multiplicative.toAdd (WithZero.unzero h)

lemma adeleOrd_of_ne_zero {a : FiniteAdeleRing R K} {v : HeightOneSpectrum R}
    (h : Valued.v (a v) ≠ 0) :
    adeleOrd a v = - Multiplicative.toAdd (WithZero.unzero h) :=
  dif_neg h

lemma adeleOrd_of_valued_zero {a : FiniteAdeleRing R K} {v : HeightOneSpectrum R}
    (h : Valued.v (a v) = 0) : adeleOrd a v = 0 :=
  dif_pos h

/-- If the `v`-component is a unit of `𝓞_v` (valuation `1`), the exponent vanishes.
This is the `adeleOrd` analogue of `ideleOrd_eq_zero_of_valued_eq_one`. -/
lemma adeleOrd_eq_zero_of_valued_eq_one {a : FiniteAdeleRing R K} {v : HeightOneSpectrum R}
    (h : Valued.v (a v) = 1) : adeleOrd a v = 0 := by
  have h0 : Valued.v (a v) ≠ 0 := by rw [h]; exact one_ne_zero
  rw [adeleOrd_of_ne_zero h0]
  have hunit : WithZero.unzero h0 = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h, WithZero.coe_one]
  rw [hunit, toAdd_one, neg_zero]

/-- The places where `adeleOrd a` is nonzero are among those where the local
valuation differs from `1`; for a finite adele these form a finite set. -/
lemma adeleOrd_ne_zero_subset (a : FiniteAdeleRing R K) :
    {v : HeightOneSpectrum R | adeleOrd a v ≠ 0} ⊆
      Function.mulSupport (fun v => Valued.v (a v)) := by
  intro v hv
  simp only [Set.mem_setOf_eq, Function.mem_mulSupport, ne_eq] at hv ⊢
  exact fun hval1 => hv (adeleOrd_eq_zero_of_valued_eq_one hval1)

/-- The local valuation recovered from the exponent:
`Valued.v (a v) = exp (-adeleOrd a v)` whenever the component is nonzero (with the
Mathlib convention `Valued.v π = exp (-1)` for a uniformizer `π`). -/
lemma valued_eq_exp_neg_adeleOrd {a : FiniteAdeleRing R K} {v : HeightOneSpectrum R}
    (h : Valued.v (a v) ≠ 0) :
    Valued.v (a v) = WithZero.exp (-(adeleOrd a v)) := by
  rw [adeleOrd_of_ne_zero h, neg_neg]
  exact (WithZero.coe_unzero h).symm

/-- The exponent `ord_v(x_v)` of the `v`-component of a finite idele `x`: this is
just `adeleOrd` of the underlying adele, the junk case never occurring since the
components of an idele are units (nonzero). -/
noncomputable def ideleOrd (x : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) : ℤ :=
  adeleOrd (x : FiniteAdeleRing R K) v

/-- Bridge: on a finite idele the exponent has no junk case. -/
lemma ideleOrd_eq (x : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    ideleOrd x v = - Multiplicative.toAdd (WithZero.unzero (valued_component_ne_zero x v)) :=
  adeleOrd_of_ne_zero (valued_component_ne_zero x v)

@[simp]
lemma ideleOrd_one (v : HeightOneSpectrum R) :
    ideleOrd (1 : (FiniteAdeleRing R K)ˣ) v = 0 := by
  have h : WithZero.unzero (valued_component_ne_zero (1 : (FiniteAdeleRing R K)ˣ) v) = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_one, Units.val_one, one_apply, map_one]
  rw [ideleOrd_eq, h, toAdd_one, neg_zero]

lemma ideleOrd_mul (x y : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    ideleOrd (x * y) v = ideleOrd x v + ideleOrd y v := by
  have key : WithZero.unzero (valued_component_ne_zero (x * y) v)
      = WithZero.unzero (valued_component_ne_zero x v)
        * WithZero.unzero (valued_component_ne_zero y v) := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_mul, WithZero.coe_unzero]
    rw [Units.val_mul, mul_apply]
    exact map_mul Valued.v _ _
  rw [ideleOrd_eq, ideleOrd_eq, ideleOrd_eq, key, toAdd_mul, neg_add]

/-- If the local component is integral both for `x` and for `x⁻¹`, then `ord_v = 0`. -/
lemma ideleOrd_eq_zero_of_valued_eq_one (x : (FiniteAdeleRing R K)ˣ) {v : HeightOneSpectrum R}
    (h : Valued.v ((x : FiniteAdeleRing R K) v) = 1) : ideleOrd x v = 0 := by
  have hunit : WithZero.unzero (valued_component_ne_zero x v) = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_one, h]
  rw [ideleOrd_eq, hunit, toAdd_one, neg_zero]

/-- The exponents `ord_v(x_v)` vanish for all but finitely many `v`: the bad set is
contained in the (finite) sets of primes where `x` or `x⁻¹` fails to be integral. -/
lemma ideleOrd_finite (x : (FiniteAdeleRing R K)ˣ) :
    {v : HeightOneSpectrum R | ideleOrd x v ≠ 0}.Finite := by
  apply Set.Finite.subset
    ((Filter.eventually_cofinite.mp (↑x : FiniteAdeleRing R K).2).union
      (Filter.eventually_cofinite.mp (↑x⁻¹ : FiniteAdeleRing R K).2))
  intro v hv
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine hv (ideleOrd_eq_zero_of_valued_eq_one x ?_)
  -- both components integral ⇒ both valuations ≤ 1; their product is 1 ⇒ both are 1.
  have ha1 : Valued.v ((↑x : FiniteAdeleRing R K) v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp h1
  have hb1 : Valued.v ((↑x⁻¹ : FiniteAdeleRing R K) v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp h2
  have hab : Valued.v ((↑x : FiniteAdeleRing R K) v) *
      Valued.v ((↑x⁻¹ : FiniteAdeleRing R K) v) = 1 := by
    rw [← map_mul, ← mul_apply, x.mul_inv, one_apply, map_one]
  refine le_antisymm ha1 ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v ((↑x : FiniteAdeleRing R K) v) *
          Valued.v ((↑x⁻¹ : FiniteAdeleRing R K) v) := hab.symm
    _ ≤ Valued.v ((↑x : FiniteAdeleRing R K) v) * 1 := by gcongr
    _ = Valued.v ((↑x : FiniteAdeleRing R K) v) := mul_one _

/-! ### The fractional ideal attached to a family of exponents

The construction `∏ᶠ v, 𝔭_v ^ (n v)` of an invertible fractional ideal from a
finitely supported family of integer exponents is the common core shared by the
idele-to-ideal map (below, via `ideleOrd`) and the Blichfeldt–Minkowski argument
(`Approximation.Blichfeldt`, via `adeleOrd`). -/

lemma asIdealZpow_mulSupport_subset (n : HeightOneSpectrum R → ℤ) :
    (Function.mulSupport fun v : HeightOneSpectrum R =>
      (v.asIdeal : FractionalIdeal R⁰ K) ^ n v) ⊆ {v | n v ≠ 0} := by
  intro v hv
  simp only [Function.mem_mulSupport, ne_eq, Set.mem_setOf_eq] at hv ⊢
  intro h0
  exact hv (by rw [h0, zpow_zero])

/-- The invertible fractional ideal `∏ᶠ v, 𝔭_v ^ (n v)` attached to a finitely
supported family of integer exponents `n`. -/
noncomputable def fractionalIdealOfExps (n : HeightOneSpectrum R → ℤ)
    (hn : {v : HeightOneSpectrum R | n v ≠ 0}.Finite) : (FractionalIdeal R⁰ K)ˣ :=
  (show (∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ n v) ≠ 0 by
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (Set.Subset.refl _)
      (hn.subset (asIdealZpow_mulSupport_subset n))]
    exact Finset.prod_ne_zero_iff.mpr fun v _ =>
      zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)).isUnit.unit

@[simp]
lemma fractionalIdealOfExps_coe (n : HeightOneSpectrum R → ℤ)
    (hn : {v : HeightOneSpectrum R | n v ≠ 0}.Finite) :
    (fractionalIdealOfExps (K := K) n hn : FractionalIdeal R⁰ K) =
      ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ n v :=
  IsUnit.unit_spec _

/-- The `v`-adic count of `fractionalIdealOfExps n` is the exponent `n v`. -/
lemma count_fractionalIdealOfExps (n : HeightOneSpectrum R → ℤ)
    (hn : {v : HeightOneSpectrum R | n v ≠ 0}.Finite) (v : HeightOneSpectrum R) :
    count K v (fractionalIdealOfExps (K := K) n hn : FractionalIdeal R⁰ K) = n v := by
  rw [fractionalIdealOfExps_coe]
  exact count_finprod K v n (Filter.eventually_cofinite.mpr hn)

/-- **Membership bound for `fractionalIdealOfExps`.** A nonzero `x ∈ K` lying in the
fractional ideal `∏ᶠ v, 𝔭_v ^ (n v)` has `v`-adic valuation at most `exp (-(n v))`
at every place `v`. This is the analytic input to the Blichfeldt–Minkowski lemma:
applied with `n = adeleOrd a` it says `v.valuation K x ≤ Valued.v (a v)`. -/
lemma valuation_le_exp_neg_of_mem_fractionalIdealOfExps (n : HeightOneSpectrum R → ℤ)
    (hn : {v : HeightOneSpectrum R | n v ≠ 0}.Finite) {x : K} (hx : x ≠ 0)
    (hx_mem : x ∈ (fractionalIdealOfExps (K := K) n hn : FractionalIdeal R⁰ K))
    (v : HeightOneSpectrum R) :
    v.valuation K x ≤ WithZero.exp (-(n v)) := by
  -- `spanSingleton x ≤ fractionalIdealOfExps n`, so `n v = count (…) ≤ count (spanSingleton x)`.
  have h_span_ne : FractionalIdeal.spanSingleton R⁰ x ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx
  have h_count_le :=
    FractionalIdeal.count_mono K v h_span_ne (FractionalIdeal.spanSingleton_le_iff_mem.mpr hx_mem)
  rw [count_fractionalIdealOfExps (K := K) n hn v] at h_count_le
  -- `v.valuation K x = exp (-count K v (spanSingleton x))`, via the `mk'` decomposition of `x`.
  have hvalx_eq : v.valuation K x =
      WithZero.exp (-(FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x))) := by
    obtain ⟨⟨m, d⟩, hnd⟩ := IsLocalization.surj R⁰ x
    have hd_ne : (d : R) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    have hd_map_ne : algebraMap R K ↑d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have hm_ne : m ≠ 0 := by
      intro hm
      simp only [hm, map_zero] at hnd
      exact hx (mul_right_cancel₀ hd_map_ne (by simp [hnd]))
    have hx_eq : x = IsLocalization.mk' K m d :=
      IsLocalization.eq_mk'_iff_mul_eq.mpr hnd
    have haJ : FractionalIdeal.spanSingleton R⁰ x =
        FractionalIdeal.spanSingleton R⁰ ((algebraMap R K ↑d)⁻¹) *
        ↑(Ideal.span {m} : Ideal R) := by
      rw [hx_eq, IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm,
          ← FractionalIdeal.spanSingleton_mul_spanSingleton,
          ← FractionalIdeal.coeIdeal_span_singleton]
    have h_cw := FractionalIdeal.count_well_defined K v h_span_ne haJ
    rw [hx_eq, HeightOneSpectrum.valuation_of_mk',
        v.intValuation_if_neg hm_ne, v.intValuation_if_neg hd_ne,
        ← WithZero.exp_sub, WithZero.exp_inj, ← hx_eq, h_cw]
    ring
  rw [hvalx_eq, WithZero.exp_le_exp]
  linarith

/-- **The idele-to-fractional-ideal homomorphism** `I_K → J_K`,
`(x_v)_v ↦ ∏_v 𝔭_v ^ ord_v(x_v)`, as a group homomorphism from the (finite)
idele group to the group of invertible fractional ideals. Built on the shared
`fractionalIdealOfExps` construction. -/
noncomputable def ideleToFractionalIdeal :
    (FiniteAdeleRing R K)ˣ →* (FractionalIdeal R⁰ K)ˣ where
  toFun x := fractionalIdealOfExps (ideleOrd x) (ideleOrd_finite x)
  map_one' := by
    apply Units.ext
    rw [fractionalIdealOfExps_coe, Units.val_one]
    simp only [ideleOrd_one, zpow_zero, finprod_one]
  map_mul' x y := by
    apply Units.ext
    rw [Units.val_mul, fractionalIdealOfExps_coe, fractionalIdealOfExps_coe,
      fractionalIdealOfExps_coe, ← finprod_mul_distrib
        ((ideleOrd_finite x).subset (asIdealZpow_mulSupport_subset (ideleOrd x)))
        ((ideleOrd_finite y).subset (asIdealZpow_mulSupport_subset (ideleOrd y)))]
    refine finprod_congr fun v => ?_
    rw [ideleOrd_mul, zpow_add₀ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)]

@[simp]
lemma ideleToFractionalIdeal_coe (x : (FiniteAdeleRing R K)ˣ) :
    (ideleToFractionalIdeal x : FractionalIdeal R⁰ K) =
      ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ ideleOrd x v :=
  fractionalIdealOfExps_coe (ideleOrd x) (ideleOrd_finite x)

/-- The `v`-adic count of the image fractional ideal is exactly `ord_v(x_v)`. -/
theorem count_ideleToFractionalIdeal (x : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    count K v (ideleToFractionalIdeal x : FractionalIdeal R⁰ K) = ideleOrd x v :=
  count_fractionalIdealOfExps (ideleOrd x) (ideleOrd_finite x) v

/-- `ord_v(x_v) = 0` precisely when the `v`-component is a unit of the valuation
ring `𝓞_v` (valuation `1`). -/
lemma ideleOrd_eq_zero_iff (x : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    ideleOrd x v = 0 ↔ Valued.v ((x : FiniteAdeleRing R K) v) = 1 := by
  refine ⟨fun h => ?_, ideleOrd_eq_zero_of_valued_eq_one x⟩
  have hu : WithZero.unzero (valued_component_ne_zero x v) = 1 := by
    rw [ideleOrd_eq, neg_eq_zero] at h
    rw [← ofAdd_toAdd (WithZero.unzero (valued_component_ne_zero x v)), h, ofAdd_zero]
  rw [← WithZero.coe_unzero (valued_component_ne_zero x v), hu, WithZero.coe_one]

/-- **The kernel** of `I_K → J_K` consists of the ideles with `ord_v = 0` at every
place. -/
theorem mem_ker_ideleToFractionalIdeal {x : (FiniteAdeleRing R K)ˣ} :
    x ∈ ideleToFractionalIdeal.ker ↔ ∀ v, ideleOrd x v = 0 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h v
    have hc := count_ideleToFractionalIdeal x v
    rw [h, Units.val_one, count_one] at hc
    exact hc.symm
  · intro h
    apply Units.ext
    rw [ideleToFractionalIdeal_coe, Units.val_one]
    simp only [h, zpow_zero, finprod_one]

/-- **The kernel**, equivalently: the ideles all of whose components are units of
the valuation ring `𝓞_v` (the maximal compact subgroup `∏_v 𝓞_v^×`). -/
theorem mem_ker_ideleToFractionalIdeal_iff_valued {x : (FiniteAdeleRing R K)ˣ} :
    x ∈ ideleToFractionalIdeal.ker ↔ ∀ v, Valued.v ((x : FiniteAdeleRing R K) v) = 1 := by
  rw [mem_ker_ideleToFractionalIdeal]
  exact forall_congr' fun v => ideleOrd_eq_zero_iff x v

/-- The idele which is `π_v ^ (n v)` at each place `v`, for a finitely-supported
exponent function `n`. It realizes any prescribed family of valuations. -/
noncomputable def mkIdele (n : HeightOneSpectrum R → ℤ)
    (hn : {v : HeightOneSpectrum R | n v ≠ 0}.Finite) : (FiniteAdeleRing R K)ˣ where
  val := ⟨fun v => (v.adicCompletionUniformizer K) ^ n v, by
    apply Filter.eventually_cofinite.mpr
    apply Set.Finite.subset hn
    intro v hv hn0
    simp only [Set.mem_setOf_eq] at hv
    exact hv (by rw [hn0, zpow_zero]; exact one_mem _)⟩
  inv := ⟨fun v => (v.adicCompletionUniformizer K) ^ (- n v), by
    apply Filter.eventually_cofinite.mpr
    apply Set.Finite.subset hn
    intro v hv hn0
    simp only [Set.mem_setOf_eq] at hv
    exact hv (by rw [hn0, neg_zero, zpow_zero]; exact one_mem _)⟩
  val_inv := by
    ext v
    change (v.adicCompletionUniformizer K) ^ n v * (v.adicCompletionUniformizer K) ^ (-n v) = 1
    rw [← zpow_add₀ (v.adicCompletionUniformizer_ne_zero K), add_neg_cancel, zpow_zero]
  inv_val := by
    ext v
    change (v.adicCompletionUniformizer K) ^ (-n v) * (v.adicCompletionUniformizer K) ^ n v = 1
    rw [← zpow_add₀ (v.adicCompletionUniformizer_ne_zero K), neg_add_cancel, zpow_zero]

@[simp]
lemma mkIdele_coe_apply (n : HeightOneSpectrum R → ℤ)
    (hn : {v : HeightOneSpectrum R | n v ≠ 0}.Finite) (v : HeightOneSpectrum R) :
    ((mkIdele (K := K) n hn : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v =
      (v.adicCompletionUniformizer K) ^ n v :=
  rfl

/-- The idele `mkIdele n` has `ord_v = n v` at every place: it realizes any
prescribed (finitely supported) family of valuations. -/
lemma ideleOrd_mkIdele (n : HeightOneSpectrum R → ℤ)
    (hn : {v : HeightOneSpectrum R | n v ≠ 0}.Finite) (v : HeightOneSpectrum R) :
    ideleOrd (mkIdele (K := K) n hn) v = n v := by
  have hu : WithZero.unzero (valued_component_ne_zero (mkIdele (K := K) n hn) v)
      = Multiplicative.ofAdd (-1 : ℤ) ^ n v := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_zpow, mkIdele_coe_apply, map_zpow₀,
      v.adicCompletionUniformizer_spec K]
  rw [ideleOrd_eq, hu, toAdd_zpow, toAdd_ofAdd]
  ring

/-- **The idele-to-fractional-ideal map is surjective.** Every invertible
fractional ideal `I = ∏ᶠ v, 𝔭_v ^ count_v(I)` is the image of the idele which is a
`count_v(I)`-th power of a uniformizer at each place. -/
theorem ideleToFractionalIdeal_surjective :
    Function.Surjective (ideleToFractionalIdeal (R := R) (K := K)) := by
  intro I
  have hI : (I : FractionalIdeal R⁰ K) ≠ 0 := I.ne_zero
  have hn : {v : HeightOneSpectrum R | count K v (I : FractionalIdeal R⁰ K) ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (finite_factors (I : FractionalIdeal R⁰ K))
  refine ⟨mkIdele (fun v => count K v (I : FractionalIdeal R⁰ K)) hn, ?_⟩
  apply Units.ext
  rw [ideleToFractionalIdeal_coe]
  simp only [ideleOrd_mkIdele]
  exact finprod_heightOneSpectrum_factorization' (K := K) hI

/-- **Injectivity criterion.** The map is injective precisely when the only idele
all of whose components are units of `𝓞_v` is the trivial one. Since this kernel —
the maximal compact subgroup `∏_v 𝓞_v^×` — is in general large, the map is
typically **not** injective. -/
theorem ideleToFractionalIdeal_injective_iff :
    Function.Injective (ideleToFractionalIdeal (R := R) (K := K)) ↔
    ∀ x : (FiniteAdeleRing R K)ˣ,
      (∀ v, Valued.v ((x : FiniteAdeleRing R K) v) = 1) → x = 1 := by
  rw [injective_iff_map_eq_one ideleToFractionalIdeal]
  refine forall_congr' fun x => imp_congr_left ?_
  rw [← mem_ker_ideleToFractionalIdeal_iff_valued]
  exact MonoidHom.mem_ker.symm

/-- **The map is not injective** as soon as some completion `K_v` has a unit of
valuation `1` (a unit of `𝓞_v`) other than `1` — e.g. `-1` whenever `-1 ≠ 1`.
Such a unit, placed at the single place `v`, is a nontrivial element of the
kernel. -/
theorem ideleToFractionalIdeal_not_injective
    {v : HeightOneSpectrum R} (α : (v.adicCompletion K)ˣ)
    (hα1 : Valued.v (α : v.adicCompletion K) = 1) (hα : (α : v.adicCompletion K) ≠ 1) :
    ¬ Function.Injective (ideleToFractionalIdeal (R := R) (K := K)) := by
  classical
  rw [ideleToFractionalIdeal_injective_iff]
  intro hinj
  -- The local unit `α` at `v` is a nontrivial element of the kernel.
  refine hα ?_
  have hker : ∀ w, Valued.v ((localUnit K α : FiniteAdeleRing R K) w) = 1 := by
    intro w
    obtain rfl | hw := eq_or_ne w v
    · rw [localUnit_eval_of_eq]; exact hα1
    · rw [localUnit_eval_of_ne K α w hw, map_one]
  have h1 : localUnit K α = 1 := hinj _ hker
  have h2 := congrArg (fun u : (FiniteAdeleRing R K)ˣ => (u : FiniteAdeleRing R K) v) h1
  simp only [localUnit_eval_of_eq, Units.val_one, one_apply] at h2
  exact h2

/-- **Noether's first isomorphism theorem for the idele-to-ideal map.**
The group of invertible fractional ideals is the quotient of the (finite) idele
group by the everywhere-units `∏_v 𝓞_v^×`:
\[
  I_K \,/\, \textstyle\prod_v 𝓞_v^\times \;\cong\; J_K .
\]
This is the (finite) idele-class–to–ideal-class identification. -/
noncomputable def fractionalIdealEquivQuotient :
    (FiniteAdeleRing R K)ˣ ⧸ ideleToFractionalIdeal.ker ≃* (FractionalIdeal R⁰ K)ˣ :=
  QuotientGroup.quotientKerEquivOfSurjective ideleToFractionalIdeal
    ideleToFractionalIdeal_surjective

@[simp]
lemma fractionalIdealEquivQuotient_mk (x : (FiniteAdeleRing R K)ˣ) :
    fractionalIdealEquivQuotient (QuotientGroup.mk x) = ideleToFractionalIdeal x :=
  rfl

end IsDedekindDomain.FiniteAdeleRing
