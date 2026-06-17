import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.NumberTheory.NumberField.FinitePlaces

open NumberField IsDedekindDomain WithZero NumberField.mixedEmbedding

open scoped nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def bmIdeal' (a : FiniteAdeleRing (𝓞 K) K)
    (h_fin : (Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      Valued.v (a v))).Finite) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ := by
  let exps : HeightOneSpectrum (𝓞 K) → ℤ := fun v =>
    if h : Valued.v (a v) = 0 then 0
    else -(Multiplicative.toAdd (WithZero.unzero h))
  -- Show the mulSupport of the zpow function is finite
  have h_ms : (Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ exps v)).Finite := by
    apply Set.Finite.subset h_fin
    intro v hv
    simp only [Function.mem_mulSupport, ne_eq] at hv
    simp only [Function.mem_mulSupport, ne_eq]
    intro hval
    apply hv
    have hne : Valued.v (a v) ≠ 0 := by rw [hval]; exact one_ne_zero
    simp only [exps, dif_neg hne]
    have hunzero : WithZero.unzero hne = 1 := by
      apply WithZero.coe_injective
      rw [WithZero.coe_unzero, hval, WithZero.coe_one]
    rw [hunzero, toAdd_one, neg_zero, zpow_zero]
  -- Show the finprod ≠ 0
  have hI_ne : (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ exps v) ≠ 0 := by
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (Set.Subset.refl _) h_ms]
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  exact hI_ne.isUnit.unit
