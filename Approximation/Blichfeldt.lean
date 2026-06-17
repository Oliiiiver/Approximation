import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.FinitePlaces
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Topology.Algebra.InfiniteSum.Order
import FLT.NumberField.AdeleRing
import Approximation.IdeleToIdeal

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

open scoped BigOperators
open scoped ENNReal NNReal nonZeroDivisors
open Filter Topology MeasureTheory
open NumberField IsDedekindDomain WithZero
open NumberField.mixedEmbedding

/-!
# The Blichfeldt–Minkowski lemma for the adele ring

This file sets up the adele-ring infrastructure shared by the strong
approximation development — the diagonal embedding `diag : K →+* 𝔸 K`, the adelic
`Norm` instances, and the bridging lemma `norm_eq_finprod_mul_prod` — and proves
the **Blichfeldt–Minkowski lemma** `blichfeldt_minkowski` (Neukirch ANT §II.25,
Lemma 25.14): an adele of large enough norm can be shifted by an element of `K`
into the unit box at every place.

The deep input is Minkowski's convex body theorem
(`NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt`); the fractional ideal
`bmIdeal` attached to a finite adele is built from `fractionalIdealOfExps`
(`Approximation.IdeleToIdeal`). This file is **sorry-free**.
-/

namespace StrongApproximation

open Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

open scoped NumberField.AdeleRing

/-! ### The adele ring and the diagonal embedding -/

/-- The diagonal embedding K ↪ 𝔸_K as a ring homomorphism. -/
abbrev diag : K →+* 𝔸 K := algebraMap K (𝔸 K)

/-! ### The adelic norm

Following the FLT design (`Norm` instances with `‖x‖ = ‖x.1‖ * ‖x.2‖` on the adele
ring), we equip the infinite adele ring, the finite adele ring and the full adele
ring with `Norm` instances computing the **idele modulus**:
- on `InfiniteAdeleRing K`: `‖x‖ = ∏ w, ‖x w‖ ^ w.mult` (the multiplicity accounts
  for complex places, where the modulus is the square of the absolute value);
- on `FiniteAdeleRing (𝓞 K) K`: `‖x‖ = ∏' v, ‖x v‖` (a `tprod`: for finite adeles
  the defining net is eventually decreasing, so the product always converges; it is
  0 when some component vanishes or infinitely many components are non-units, and
  equals the finite product `∏ᶠ` on ideles of finite mulSupport);
- on `𝔸 K`: the product `‖x.1‖ * ‖x.2‖` of the two.

For x ∈ K×, ‖diag x‖ = 1 (product formula). On the unit group `(𝔸 K)ˣ` this norm
agrees with the Haar modulus character `MeasureTheory.ringHaarChar` (FLT) for ideles
of finite mulSupport; we use the explicit form because the Blichfeldt–Minkowski
proof compares it directly with `FractionalIdeal.absNorm` and `convexBodyLT` volumes.

NOTE: these instances replicate Mathlib-in-progress definitions by S. Mercuri —
the infinite-adele norm is merged in Mathlib master (PR #36204), the finite-adele
norm is PR #36275, the adele-ring norm is on its way. Once the project updates to
a Mathlib providing them, delete these and use Mathlib's. -/

/-- The modulus norm on the infinite adele ring: `∏ w, ‖x w‖ ^ w.mult`
    (matches Mathlib PR #36204, merged). -/
instance : Norm (InfiniteAdeleRing K) where
  norm x := ∏ w : InfinitePlace K, ‖x w‖ ^ w.mult

theorem infiniteAdele_norm_def (x : InfiniteAdeleRing K) :
    ‖x‖ = ∏ w : InfinitePlace K, ‖x w‖ ^ w.mult := rfl

/-- The modulus norm on the finite adele ring: `∏' v, ‖x v‖`
    (matches Mathlib PR #36275). -/
instance : Norm (FiniteAdeleRing (𝓞 K) K) where
  norm x := ∏' v : HeightOneSpectrum (𝓞 K), ‖x v‖

theorem finiteAdele_norm_def (x : FiniteAdeleRing (𝓞 K) K) :
    ‖x‖ = ∏' v : HeightOneSpectrum (𝓞 K), ‖x v‖ := rfl

/-- On finite adeles whose norms have finite mulSupport (e.g. ideles), the norm
    is the finite product `∏ᶠ v, ‖x v‖`. -/
theorem finiteAdele_norm_eq_finprod (x : FiniteAdeleRing (𝓞 K) K)
    (h : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖x v‖).Finite) :
    ‖x‖ = ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖x v‖ :=
  (finiteAdele_norm_def K x).trans (tprod_eq_finprod h)

/-- The adelic norm (idele modulus): the product of the infinite and finite parts. -/
instance : Norm (𝔸 K) where
  norm x := ‖x.1‖ * ‖x.2‖

theorem norm_def (x : 𝔸 K) : ‖x‖ = ‖x.1‖ * ‖x.2‖ := rfl

/-- The mulSupport of the local norms is finite whenever the mulSupport of the
    local valuations is (`‖x v‖ = 1 ↔ Valued.v (x v) = 1`). -/
lemma norm_mulSupport_finite_of_valued {x : FiniteAdeleRing (𝓞 K) K}
    (h : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      Valued.v (x v)).Finite) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖x v‖).Finite := by
  apply Set.Finite.subset h
  intro v hv
  simp only [Function.mem_mulSupport, ne_eq] at hv ⊢
  intro hval_one
  exact hv (le_antisymm
    (Valued.toNormedField.norm_le_one_iff.mpr hval_one.le)
    (Valued.toNormedField.one_le_norm_iff.mpr hval_one.ge))

/-- Unfolded form of the adelic norm for adeles with finite valuation mulSupport,
    in the order (finite part) × (infinite part) used throughout the
    Blichfeldt–Minkowski argument. -/
theorem norm_eq_finprod_mul_prod (x : 𝔸 K)
    (h : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      Valued.v (x.2 v)).Finite) :
    ‖x‖ = (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖x.2 v‖) *
      ∏ w : InfinitePlace K, ‖x.1 w‖ ^ w.mult := by
  rw [norm_def, finiteAdele_norm_eq_finprod K x.2 (norm_mulSupport_finite_of_valued K h),
      infiniteAdele_norm_def, mul_comm]

/-! ### Auxiliary norm lemmas (needed by Blichfeldt-Minkowski) -/

/-- The finite-place component of the diagonal embedding equals the valuation.
    Valued.v ((diag K x).2 v) = v.valuation K x -/
lemma valuedAdicCompletion_diag' (x : K) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((diag K x).2 v) = v.valuation K x := by
  have h1 : (diag K x).2 v = (x : v.adicCompletion K) :=
    NumberField.AdeleRing.algebraMap_snd_apply (𝓞 K) K x v
  rw [h1]
  exact @IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (𝓞 K) _ _ K _ _ _ v x

/-! ### Blichfeldt-Minkowski and coset decomposition -/

/-- **`absNorm` of the Blichfeldt–Minkowski fractional ideal** — the number-field
input to the lemma. For a finite adele `a` with everywhere-nonzero finite
components, the absolute norm of `∏ᶠ v, 𝔭_v ^ adeleOrd a v` is the reciprocal of
`∏ᶠ v, ‖a v‖`. The fractional ideal itself and its membership bound are the shared,
general-Dedekind constructions of `Approximation.IdeleToIdeal` (`fractionalIdealOfExps`,
`adeleOrd`); only this `absNorm` computation needs the number-field structure. -/
private lemma absNorm_fractionalIdealOfExps_adeleOrd (a : FiniteAdeleRing (𝓞 K) K)
    (hsupp : {v : HeightOneSpectrum (𝓞 K) | FiniteAdeleRing.adeleOrd a v ≠ 0}.Finite)
    (h_ne : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (a v) ≠ 0) :
    (FractionalIdeal.absNorm
        (FiniteAdeleRing.fractionalIdealOfExps (K := K) (FiniteAdeleRing.adeleOrd a) hsupp).1 :
          ℝ) =
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a v‖)⁻¹ := by
  -- 1. Finite support of v ↦ (↑v.asIdeal)^{n_v}
  have h_ms : (Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FiniteAdeleRing.adeleOrd a v)).Finite :=
    hsupp.subset (FiniteAdeleRing.asIdealZpow_mulSupport_subset (FiniteAdeleRing.adeleOrd a))
  -- 2. Rewrite the fractional ideal as its finprod, then push (cast ∘ absNorm) through it
  rw [FiniteAdeleRing.fractionalIdealOfExps_coe]
  -- Use ℝ-valued composite MonoidHom to push both absNorm and cast through finprod at once
  have h_key : ∀ I : FractionalIdeal (𝓞 K)⁰ K,
      (FractionalIdeal.absNorm I : ℝ) =
      ((Rat.castHom ℝ).toMonoidHom.comp FractionalIdeal.absNorm.toMonoidHom) I := fun I => rfl
  rw [h_key, ((Rat.castHom ℝ).toMonoidHom.comp FractionalIdeal.absNorm.toMonoidHom).map_finprod
      h_ms]
  simp only [MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  -- 3. Rewrite RHS using finprod_inv_distrib
  rw [← finprod_inv_distrib]
  -- 4. Pointwise equality for each v
  congr 1; ext v
  -- Goal: (Rat.castHom ℝ) (↑FractionalIdeal.absNorm (↑v.asIdeal ^ n_v)) = ‖a v‖⁻¹
  -- Normalize: (Rat.castHom ℝ) (↑absNorm x) ≡ (absNorm x : ℝ) definitionally
  change (FractionalIdeal.absNorm
        ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FiniteAdeleRing.adeleOrd a v) : ℝ)
      = ‖a v‖⁻¹
  -- 4a. Apply map_zpow₀ (now absNorm appears without ↑ coercion, so rw matches)
  rw [map_zpow₀ (FractionalIdeal.absNorm : FractionalIdeal (𝓞 K)⁰ K →*₀ ℚ),
      FractionalIdeal.coeIdeal_absNorm]
  push_cast
  -- Goal: (Ideal.absNorm v.asIdeal : ℝ)^{FiniteAdeleRing.adeleOrd a v} = ‖a v‖⁻¹
  simp only [FiniteAdeleRing.adeleOrd, dif_neg (h_ne v), zpow_neg]
  rw [inv_inj]
  -- Goal: ‖a v‖ = (Ideal.absNorm v.asIdeal : ℝ)^{(unzero (h_ne v)).toAdd}
  rw [show ‖a v‖ =
      (WithZeroMulInt.toNNReal (RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero v)
        (Valued.v (a v)) : ℝ) from rfl]
  rw [WithZeroMulInt.toNNReal_neg_apply (RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero v)
      (h_ne v), NNReal.coe_zpow]
  push_cast
  rfl

/-- **Adelic Blichfeldt-Minkowski Lemma** (Lemma 25.14, corrected).

    There exists a constant B > 0 such that for any adele a with FINITE mulSupport
    (only finitely many finite places where Valued.v(a.2 v) ≠ 1) and ‖a‖ > B,
    there exists x ∈ K× with |x|_v ≤ |a|_v at all places v.

    The finiteness hypothesis is necessary: without it the theorem is FALSE.
    Counterexample: a = (π_v)_v (uniformizer at every finite place) has
    ‖a‖ = 1 (infinite finprod = 1) but any x ≠ 0 satisfying
    v(x) ≤ v(π_v) < 1 for ALL v lies in ∩_v 𝔪_v = {0}, contradiction. -/
lemma blichfeldt_minkowski :
    ∃ (B : ℝ), 0 < B ∧
    ∀ (a : 𝔸 K),
      -- Finiteness hypothesis: only finitely many finite places have non-unit valuation.
      -- Without this, the finprod in the adelic norm returns 1 for infinite-support
      -- adeles, making the theorem FALSE (counterexample: uniformizer adele (π_v)_v).
      (Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => Valued.v (a.2 v))).Finite →
      B < ‖a‖ →
      ∃ (x : K), x ≠ 0 ∧
        (∀ v : HeightOneSpectrum (𝓞 K),
            Valued.v ((diag K x).2 v) ≤ Valued.v (a.2 v)) ∧
        (∀ w : InfinitePlace K,
            ‖(diag K x).1 w‖ ≤ ‖a.1 w‖) := by
  -- The Minkowski bound: B = minkowskiBound(𝓞_K) / convexBodyLTFactor(K)
  use (minkowskiBound K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) /
       (convexBodyLTFactor K : ℝ≥0∞)).toReal
  refine ⟨?_, fun a h_fin h_large => ?_⟩
  · -- B > 0: ratio of two positive finite quantities
    apply ENNReal.toReal_pos
    · exact (ENNReal.div_pos (minkowskiBound_pos K 1).ne' ENNReal.coe_ne_top).ne'
    · exact ENNReal.div_ne_top (minkowskiBound_lt_top K 1).ne
        (ENNReal.coe_ne_zero.mpr (convexBodyLTFactor_ne_zero K))
  · -- Main proof: construct x using Blichfeldt-Minkowski / Minkowski's theorem
    -- Step 0: The fractional ideal I_a for the finite part of a, built directly from
    -- the shared `fractionalIdealOfExps` (no separate `bmIdeal` definition needed; this
    -- is the same construction underlying the idele-to-ideal map of `IdeleToIdeal`).
    have hsupp : {v : HeightOneSpectrum (𝓞 K) | FiniteAdeleRing.adeleOrd a.2 v ≠ 0}.Finite :=
      h_fin.subset (FiniteAdeleRing.adeleOrd_ne_zero_subset a.2)
    let I_a := FiniteAdeleRing.fractionalIdealOfExps (K := K) (FiniteAdeleRing.adeleOrd a.2) hsupp
    -- Step 0.5: All finite-place valuations of a.2 are nonzero.
    -- Proof: if Valued.v (a.2 w) = 0 for some w, then ‖a.2 w‖ = 0,
    -- making ∏ᶠ ‖a.2 v‖ = 0 (by finprod_eq_zero), so ‖a‖ = 0.
    -- But h_large says B < 0, while B ≥ 0 (ENNReal.toReal ≥ 0). Contradiction.
    have h_ne : ∀ w : HeightOneSpectrum (𝓞 K), Valued.v (a.2 w) ≠ 0 := by
      intro w hw
      have haw : a.2 w = 0 := by rwa [← Valuation.zero_iff Valued.v]
      have h_prod_zero : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖ = 0 :=
        finprod_eq_zero _ w (by simp [haw]) (norm_mulSupport_finite_of_valued K h_fin)
      have h_adelic_zero : ‖a‖ = 0 := by
        rw [norm_eq_finprod_mul_prod K a h_fin, h_prod_zero, zero_mul]
      rw [h_adelic_zero] at h_large
      exact absurd h_large (not_lt.mpr ENNReal.toReal_nonneg)
    -- Step 1: Show the Minkowski condition holds
    have h_mink : minkowskiBound K I_a <
        volume (convexBodyLT K (fun w => ‖a.1 w‖₊)) := by
      rw [convexBodyLT_volume]
      -- Helper: finite support of norms (from the valuation support hypothesis)
      have h_norm_fin : (Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
          ‖a.2 v‖)).Finite := norm_mulSupport_finite_of_valued K h_fin
      -- F := ∏ᶠ v, ‖a.2 v‖ > 0 (all ‖a.2 v‖ > 0 by h_ne, and finprod is finite)
      have h_F_pos : 0 < ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖ := by
        rw [finprod_eq_prod _ h_norm_fin]
        exact Finset.prod_pos (fun v _ =>
          norm_pos_iff.mpr ((Valuation.ne_zero_iff Valued.v).mp (h_ne v)))
      -- C := convexBodyLTFactor K > 0 (it is ≥ 1)
      have h_C_pos : 0 < (convexBodyLTFactor K : ℝ) :=
        NNReal.coe_pos.mpr (lt_of_lt_of_le one_pos (one_le_convexBodyLTFactor K))
      -- minkowskiBound K I_a = ofReal(absNorm I_a.1) * minkowskiBound K 1
      -- Proof: expand both sides via volume_fundamentalDomain_fractionalIdealLatticeBasis.
      have h_mink_eq : minkowskiBound K I_a =
          ENNReal.ofReal ↑(FractionalIdeal.absNorm I_a.1) * minkowskiBound K 1 := by
        have h_vol_Ia : volume (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K I_a)) =
            ENNReal.ofReal ↑(FractionalIdeal.absNorm I_a.1) *
            volume (ZSpan.fundamentalDomain (latticeBasis K)) :=
          volume_fundamentalDomain_fractionalIdealLatticeBasis K I_a
        have h_vol_1 : volume (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K 1)) =
            volume (ZSpan.fundamentalDomain (latticeBasis K)) := by
          have h := volume_fundamentalDomain_fractionalIdealLatticeBasis K
              (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
          simp only [Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one,
              ENNReal.ofReal_one, one_mul] at h
          exact h
        simp only [minkowskiBound, h_vol_Ia, h_vol_1]
        ring
      -- absNorm I_a.1 = F⁻¹  (the number-field input lemma)
      have h_absNorm : (FractionalIdeal.absNorm I_a.1 : ℝ) =
          (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖)⁻¹ :=
        absNorm_fractionalIdealOfExps_adeleOrd K a.2 hsupp h_ne
      -- Combine: minkowskiBound K I_a = ofReal(F⁻¹) * minkowskiBound K 1
      have h_mb : minkowskiBound K I_a =
          ENNReal.ofReal (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖)⁻¹ *
          minkowskiBound K 1 := by rw [h_mink_eq, h_absNorm]
      -- Convert ENNReal goal to a real-number inequality
      -- RHS = ↑(convexBodyLTFactor K) * ↑(∏ w, ‖a.1 w‖₊ ^ w.mult), which is ≠ ⊤
      rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top K I_a).ne
          (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)]
      -- Expand LHS: (minkowskiBound K I_a).toReal = F⁻¹ * (minkowskiBound K 1).toReal
      have hLHS : (minkowskiBound K I_a).toReal =
          (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖)⁻¹ * (minkowskiBound K 1).toReal := by
        rw [h_mb, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (inv_nonneg.mpr h_F_pos.le)]
      -- Expand RHS: ↑C * ↑P = C * P as reals
      have hRHS : ((↑(convexBodyLTFactor K) * ↑(∏ w : InfinitePlace K, ‖a.1 w‖₊ ^ w.mult) :
            ℝ≥0∞)).toReal =
          (convexBodyLTFactor K : ℝ) * ∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
        congr 1
        push_cast [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
        rfl
      rw [hLHS, hRHS]
      -- Goal: F⁻¹ * M < C * P  where h_large : M/C < ‖a‖ = F * P
      -- Rewrite h_large to expose M/C < F*P
      have h_large' : (minkowskiBound K 1 : ℝ≥0∞).toReal / (convexBodyLTFactor K : ℝ) <
          (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖) *
          ∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult := by
        have := h_large
        rw [ENNReal.toReal_div, ENNReal.coe_toReal,
            norm_eq_finprod_mul_prod K a h_fin] at this
        exact this
      -- M/C < F*P  ↔  M < C*(F*P)  ↔  F⁻¹*M < C*P
      rw [div_lt_iff₀ h_C_pos] at h_large'
      rw [inv_mul_lt_iff₀ h_F_pos]
      linarith [show (convexBodyLTFactor K : ℝ) * ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖) *
          ∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult) =
          (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖) *
          ((convexBodyLTFactor K : ℝ) * ∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult) from by ring]
    -- Step 2: Apply Minkowski's theorem
    obtain ⟨x, hx_mem, hx_ne, hx_bd⟩ :=
      exists_ne_zero_mem_ideal_lt K I_a h_mink
    -- Step 3: Package the result
    refine ⟨x, hx_ne, ?_, ?_⟩
    · -- Finite place condition: Valued.v((diag x).2 v) ≤ Valued.v(a.2 v) for all v
      intro v
      rw [valuedAdicCompletion_diag', FiniteAdeleRing.valued_eq_exp_neg_adeleOrd (h_ne v)]
      exact FiniteAdeleRing.valuation_le_exp_neg_of_mem_fractionalIdealOfExps
        (FiniteAdeleRing.adeleOrd a.2) hsupp hx_ne hx_mem v
    · -- Infinite place condition: ‖(diag x).1 w‖ ≤ ‖a.1 w‖ for all w.
      intro w
      have h_norm : ‖(diag K x).1 w‖ = w x := by
        simp only [NumberField.AdeleRing.algebraMap_fst_apply]
        rw [show (x : w.Completion) =
              ((WithAbs.equiv w.1).symm x : w.Completion) from rfl]
        rw [InfinitePlace.Completion.norm_coe, RingEquiv.apply_symm_apply]
      rw [h_norm]
      have hbd := hx_bd w
      exact le_of_lt (lt_of_lt_of_eq hbd (coe_nnnorm _))

end
end StrongApproximation
