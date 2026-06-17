import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.InfinitePlace.Completion

open NumberField NNReal

variable (K : Type*) [Field K] [NumberField K]

-- Test 2: The ∞-place condition as it appears in BM
example (x : K) (a : NumberField.AdeleRing (𝓞 K) K)
    (hx_bd : ∀ w : InfinitePlace K, w x < ‖a.1 w‖₊)
    (w : InfinitePlace K) :
    ‖(algebraMap K (NumberField.AdeleRing (𝓞 K) K) x).1 w‖ ≤ ‖a.1 w‖ := by
  have h_norm : ‖(algebraMap K (NumberField.AdeleRing (𝓞 K) K) x).1 w‖ = w x := by
    simp only [AdeleRing.algebraMap_fst_apply]
    rw [show (x : w.Completion) = ((WithAbs.equiv w.1).symm x : w.Completion) from rfl]
    rw [InfinitePlace.Completion.norm_coe, RingEquiv.apply_symm_apply]
  rw [h_norm]
  have hbd := hx_bd w
  -- hbd : w x < ‖a.1 w‖₊   (ℝ≥0 coercion on RHS)
  -- need: w x ≤ ‖a.1 w‖   (real norm)
  have : (‖a.1 w‖₊ : ℝ) = ‖a.1 w‖ := coe_nnnorm _
  rw [← this]
  exact le_of_lt hbd
