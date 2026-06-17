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

/-- If any finite-place component has zero valuation (i.e. the component is zero),
    the full adelic norm vanishes. Works over any number field. -/
lemma norm_eq_zero_of_component_zero (a : 𝔸 K)
    (h_fin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => Valued.v (a.2 v)).Finite)
    {w : HeightOneSpectrum (𝓞 K)} (hw : Valued.v (a.2 w) = 0) : ‖a‖ = 0 := by
  have haw : a.2 w = 0 := (Valuation.zero_iff Valued.v).mp hw
  rw [norm_eq_finprod_mul_prod K a h_fin,
      finprod_eq_zero _ w (by simp [haw]) (norm_mulSupport_finite_of_valued K h_fin), zero_mul]

/-- For an adele with positive norm, all finite-place valuations are nonzero.
    Contrapositively: a zero component forces the norm to zero. -/
lemma valued_ne_zero_of_norm_pos (a : 𝔸 K)
    (h_fin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => Valued.v (a.2 v)).Finite)
    (h_pos : 0 < ‖a‖) (v : HeightOneSpectrum (𝓞 K)) : Valued.v (a.2 v) ≠ 0 := fun hv =>
  absurd h_pos (by linarith [norm_eq_zero_of_component_zero K a h_fin hv])

/-! ### Blichfeldt-Minkowski and coset decomposition -/

/-- **`absNorm` of the Blichfeldt–Minkowski fractional ideal** — the number-field
input to the lemma. For a finite adele `a` with everywhere-nonzero finite
components, the absolute norm of `∏ᶠ v, 𝔭_v ^ adeleOrd a v` is the reciprocal of
`∏ᶠ v, ‖a v‖`. The fractional ideal itself and its membership bound are the shared,
general-Dedekind constructions of `Approximation.IdeleToIdeal` (`fractionalIdealOfExps`,
`adeleOrd`); only this `absNorm` computation needs the number-field structure. -/
lemma absNorm_fractionalIdealOfExps_adeleOrd (a : FiniteAdeleRing (𝓞 K) K)
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

/-- The Minkowski bound scales linearly with the absolute norm of the fractional ideal:
    `minkowskiBound K I = absNorm I · minkowskiBound K 1`.

    This factoring holds for any invertible fractional ideal `I` of a number field `K`
    and follows directly from `volume_fundamentalDomain_fractionalIdealLatticeBasis`.
    It isolates the ideal-theoretic scaling from the analytic Minkowski bound. -/
lemma minkowskiBound_mul_absNorm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    minkowskiBound K I =
        ENNReal.ofReal (FractionalIdeal.absNorm I.1 : ℝ) * minkowskiBound K 1 := by
  have h_vol : volume (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K I)) =
      ENNReal.ofReal ↑(FractionalIdeal.absNorm I.1) *
      volume (ZSpan.fundamentalDomain (latticeBasis K)) :=
    volume_fundamentalDomain_fractionalIdealLatticeBasis K I
  have h_one : volume (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K 1)) =
      volume (ZSpan.fundamentalDomain (latticeBasis K)) := by
    have h := volume_fundamentalDomain_fractionalIdealLatticeBasis K
        (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    simp only [Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one,
        ENNReal.ofReal_one, one_mul] at h
    exact h
  simp only [minkowskiBound, h_vol, h_one]
  ring

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
  refine ⟨(minkowskiBound K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) /
       (convexBodyLTFactor K : ℝ≥0∞)).toReal, ?_, fun a h_fin h_large => ?_⟩
  · -- B > 0: ratio of two positive finite ENNReal quantities
    exact ENNReal.toReal_pos
      (ENNReal.div_pos (minkowskiBound_pos K 1).ne' ENNReal.coe_ne_top).ne'
      (ENNReal.div_ne_top (minkowskiBound_lt_top K 1).ne
        (ENNReal.coe_ne_zero.mpr (convexBodyLTFactor_ne_zero K)))
  · -- Build the Blichfeldt fractional ideal I_a from the valuation exponents of a.2
    have hsupp : {v : HeightOneSpectrum (𝓞 K) | FiniteAdeleRing.adeleOrd a.2 v ≠ 0}.Finite :=
      h_fin.subset (FiniteAdeleRing.adeleOrd_ne_zero_subset a.2)
    let I_a := FiniteAdeleRing.fractionalIdealOfExps (K := K) (FiniteAdeleRing.adeleOrd a.2) hsupp
    -- All finite-place valuations are nonzero: B ≥ 0 < ‖a‖ forces ‖a‖ > 0,
    -- and a zero component would make ‖a‖ = 0 via norm_eq_zero_of_component_zero.
    have h_ne : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (a.2 v) ≠ 0 :=
      fun v => valued_ne_zero_of_norm_pos K a h_fin
        (ENNReal.toReal_nonneg.trans_lt h_large) v
    -- Step 1: Verify the Minkowski volume condition minkowskiBound K I_a < vol(convexBody)
    have h_mink : minkowskiBound K I_a < volume (convexBodyLT K (fun w => ‖a.1 w‖₊)) := by
      rw [convexBodyLT_volume]
      have h_norm_fin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
          ‖a.2 v‖).Finite := norm_mulSupport_finite_of_valued K h_fin
      -- F := ∏ᶠ v, ‖a.2 v‖ > 0 since each factor is positive
      have h_F_pos : 0 < ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖ := by
        rw [finprod_eq_prod _ h_norm_fin]
        exact Finset.prod_pos fun v _ =>
          norm_pos_iff.mpr ((Valuation.ne_zero_iff Valued.v).mp (h_ne v))
      have h_C_pos : 0 < (convexBodyLTFactor K : ℝ) :=
        NNReal.coe_pos.mpr (lt_of_lt_of_le one_pos (one_le_convexBodyLTFactor K))
      -- Reduce to a real inequality via ENNReal.toReal
      rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top K I_a).ne
          (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)]
      -- LHS: minkowskiBound_mul_absNorm + absNorm_fractionalIdealOfExps_adeleOrd
      -- give (minkowskiBound K I_a).toReal = F⁻¹ · (minkowskiBound K 1).toReal
      have hLHS : (minkowskiBound K I_a).toReal =
          (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖)⁻¹ * (minkowskiBound K 1).toReal := by
        rw [minkowskiBound_mul_absNorm,
            absNorm_fractionalIdealOfExps_adeleOrd K a.2 hsupp h_ne,
            ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr h_F_pos.le)]
      -- RHS: convert NNReal products to ℝ
      have hRHS : ((↑(convexBodyLTFactor K) * ↑(∏ w : InfinitePlace K,
            ‖a.1 w‖₊ ^ w.mult) : ℝ≥0∞)).toReal =
          (convexBodyLTFactor K : ℝ) * ∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
        congr 1; push_cast [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]; rfl
      rw [hLHS, hRHS]
      -- h_large gives M/C < F · P; rearrange to F⁻¹ · M < C · P
      have h_large' : (minkowskiBound K 1 : ℝ≥0∞).toReal / (convexBodyLTFactor K : ℝ) <
          (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖) *
          ∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult := by
        rwa [ENNReal.toReal_div, ENNReal.coe_toReal,
            norm_eq_finprod_mul_prod K a h_fin] at h_large
      rw [div_lt_iff₀ h_C_pos] at h_large'
      rw [inv_mul_lt_iff₀ h_F_pos]
      linarith [show (convexBodyLTFactor K : ℝ) *
          ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖) *
          ∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult) =
          (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖a.2 v‖) *
          ((convexBodyLTFactor K : ℝ) * ∏ w : InfinitePlace K, ‖a.1 w‖ ^ w.mult) from by ring]
    -- Step 2: Apply Minkowski's theorem
    obtain ⟨x, hx_mem, hx_ne, hx_bd⟩ := exists_ne_zero_mem_ideal_lt K I_a h_mink
    -- Step 3: Package finite-place and infinite-place bounds
    refine ⟨x, hx_ne, fun v => ?_, fun w => ?_⟩
    · rw [valuedAdicCompletion_diag', FiniteAdeleRing.valued_eq_exp_neg_adeleOrd (h_ne v)]
      exact FiniteAdeleRing.valuation_le_exp_neg_of_mem_fractionalIdealOfExps
        (FiniteAdeleRing.adeleOrd a.2) hsupp hx_ne hx_mem v
    · have h_norm : ‖(diag K x).1 w‖ = w x := by
        simp only [NumberField.AdeleRing.algebraMap_fst_apply]
        rw [show (x : w.Completion) = ((WithAbs.equiv w.1).symm x : w.Completion) from rfl,
            InfinitePlace.Completion.norm_coe, RingEquiv.apply_symm_apply]
      exact le_of_lt (h_norm ▸ lt_of_lt_of_eq (hx_bd w) (coe_nnnorm _))

end
end StrongApproximation
