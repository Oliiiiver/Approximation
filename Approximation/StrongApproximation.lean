import Approximation.Blichfeldt

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
# The Strong Approximation Theorem for number fields

Building on the Blichfeldt–Minkowski lemma (`Approximation.Blichfeldt`) and the
cocompactness of `K` in `𝔸 K` (`NumberField.AdeleRing.cocompact`, FLT package),
this file proves the **Strong Approximation Theorem** `strong_approximation`
(Neukirch ANT §II.25, Theorem 25.16): with one place left out, `K` is dense in
the corresponding restricted product of completions.

The proof combines `blichfeldt_minkowski`, the large-norm adele construction
`exists_adele_large_norm`, and a compact set covering `𝔸 K` modulo `K`
(`exists_compact_cover` and the bounds derived from it). This file is
**sorry-free**.
-/

namespace StrongApproximation

open Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

open scoped NumberField.AdeleRing

/-! ### The type of all places of K -/

/-- The type of all places of K: infinite places (embeddings K ↪ ℂ up to conjugation)
    and finite places (height-one primes of 𝓞 K).
    In the strong approximation theorem, exactly one place `w : Place K` is left
    unconstrained; all others lie in the approximation set S or the integrality set T. -/
abbrev Place := InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)

/-- For any infinite place `v` and real `δ > 0`, there exists a non-zero element of `v.Completion`
    with norm strictly between 0 and δ.  The construction case-splits on whether `v` is real
    (use `(ringEquivRealOfIsReal hv).symm (δ/2)`) or complex
    (use `(ringEquivComplexOfIsComplex hv).symm ((δ/2 : ℝ) : ℂ)`).
    The norm equality uses that `extensionEmbedding*` is an isometry and equals `ringEquiv*`. -/
private lemma exists_small_norm_elem (v : InfinitePlace K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ e : v.Completion, 0 < ‖e‖ ∧ ‖e‖ ≤ δ := by
  rcases InfinitePlace.isReal_or_isComplex v with hv | hv
  · -- Real case: e = (ringEquivRealOfIsReal hv).symm (δ/2)
    let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm (δ / 2)
    have h_norm : ‖e‖ = δ / 2 := by
      -- extensionEmbeddingOfIsReal is an isometry and equals ringEquivRealOfIsReal as a function
      have hi : Isometry (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv) :=
        InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv
      -- Both functions agree (ringEquivRealOfIsReal = RingEquiv.ofBijective extensionEmbedding ...)
      have h_fun_eq : ∀ x : v.Completion,
          InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x =
          (InfinitePlace.Completion.ringEquivRealOfIsReal hv) x := fun _ => rfl
      rw [← hi.norm_map_of_map_zero (map_zero _) e, h_fun_eq e,
          RingEquiv.apply_symm_apply, Real.norm_of_nonneg (le_of_lt (half_pos hδ))]
    exact ⟨e, h_norm ▸ half_pos hδ, h_norm ▸ half_le_self (le_of_lt hδ)⟩
  · -- Complex case: e = (ringEquivComplexOfIsComplex hv).symm (↑(δ/2) : ℂ)
    let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm ((δ / 2 : ℝ) : ℂ)
    have h_norm : ‖e‖ = δ / 2 := by
      -- extensionEmbedding v is an isometry and equals ringEquivComplexOfIsComplex as a function
      have hi : Isometry (InfinitePlace.Completion.extensionEmbedding v) :=
        InfinitePlace.Completion.isometry_extensionEmbedding v
      have h_fun_eq : ∀ x : v.Completion,
          InfinitePlace.Completion.extensionEmbedding v x =
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv) x := fun _ => rfl
      rw [← hi.norm_map_of_map_zero (map_zero _) e, h_fun_eq e,
          RingEquiv.apply_symm_apply, Complex.norm_real,
          Real.norm_of_nonneg (le_of_lt (half_pos hδ))]
    exact ⟨e, h_norm ▸ half_pos hδ, h_norm ▸ half_le_self (le_of_lt hδ)⟩

/-- **Existence of an adele with prescribed local size and large adelic norm.**

    Given a distinguished place `w : Place K`, approximation data at Sfin (finite) and Sinf
    (infinite), and integrality at Tfin, we find z ∈ 𝔸_K with:
    - Valued.v (z.2 v) ≤ ε v        for v ∈ Sfin  (finite approximation targets)
    - ‖z.1 w'‖ ≤ δ w'               for w' ∈ Sinf (infinite approximation targets)
    - z.2 v ∈ adicCompletionIntegers for v ∈ Tfin  (integrality)
    - finite mulSupport              (needed for blichfeldt_minkowski)
    - ‖z‖ > B                        (achieved by making the w-component large)

    Proof splits on whether w is infinite or finite:
    • `w = Sum.inl w₀` (infinite): embed n ≫ 0 at w₀ for the adelic norm; use
      elements of small prescribed norm at each Sinf place (`exists_small_norm_elem`).
    • `w = Sum.inr w_fin` (finite): place a high-order pole π₀^n at w_fin, where
      ‖π₀‖ > 1 comes from `Valued.toNontriviallyNormedField`. -/
lemma exists_adele_large_norm
    (B : ℝ)
    (w : Place K)
    (Sfin : Finset (HeightOneSpectrum (𝓞 K)))
    (Sinf : Finset (InfinitePlace K))
    (Tfin : Set (HeightOneSpectrum (𝓞 K)))
    (hwSfin : ∀ v ∈ Sfin, (Sum.inr v : Place K) ≠ w)
    (hwSinf : ∀ w' ∈ Sinf, (Sum.inl w' : Place K) ≠ w)
    (hwTfin : ∀ v ∈ Tfin, (Sum.inr v : Place K) ≠ w)
    (ε : HeightOneSpectrum (𝓞 K) → ℤᵐ⁰)
    (hε : ∀ v ∈ Sfin, (0 : ℤᵐ⁰) < ε v)
    (δ : InfinitePlace K → ℝ)
    (hδ : ∀ w' ∈ Sinf, 0 < δ w') :
    ∃ z : 𝔸 K,
      (∀ v ∈ Sfin, Valued.v (z.2 v) ≤ ε v) ∧
      (∀ w' ∈ Sinf, ‖z.1 w'‖ ≤ δ w') ∧
      (∀ v ∈ Tfin, z.2 v ∈ v.adicCompletionIntegers K) ∧
      (Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => Valued.v (z.2 v))).Finite ∧
      B < ‖z‖ ∧
      (∀ w' : InfinitePlace K, w' ∉ Sinf → (Sum.inl w' : Place K) ≠ w → ‖z.1 w'‖ ≤ 1) := by
  classical
  -- ---------------------------------------------------------------
  -- Shared setup: build pick for the Sfin-conditions.
  -- ---------------------------------------------------------------
  have h_surj : ∀ v ∈ Sfin, ∃ x : v.adicCompletion K, Valued.v x = min (ε v) 1 := fun v _ =>
    HeightOneSpectrum.valuedAdicCompletion_surjective K v (min (ε v) 1)
  let pick : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K :=
    fun v => if hv : v ∈ Sfin then Classical.choose (h_surj v hv) else 1
  have h_pick_val : ∀ v (hv : v ∈ Sfin), Valued.v (pick v) = min (ε v) 1 := by
    intro v hv; simp only [pick, dif_pos hv]
    exact Classical.choose_spec (h_surj v hv)
  have h_pick_int : ∀ v, pick v ∈ v.adicCompletionIntegers K := by
    intro v; rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hv : v ∈ Sfin
    · rw [h_pick_val v hv]; exact min_le_right _ _
    · simp [pick, hv]
  have h_pick_ne_zero : ∀ v ∈ Sfin, pick v ≠ 0 := by
    intro v hv h0; have hval := h_pick_val v hv
    rw [h0, map_zero] at hval
    exact absurd (lt_min (hε v hv) one_pos) (hval ▸ lt_irrefl _)
  have h_C_pos : 0 < ∏ v ∈ Sfin, ‖pick v‖ :=
    Finset.prod_pos (fun v hv => norm_pos_iff.mpr (h_pick_ne_zero v hv))
  have h_pick_supp : Function.mulSupport (fun v => ‖(pick v : v.adicCompletion K)‖) ⊆
      (Sfin : Set (HeightOneSpectrum (𝓞 K))) := by
    intro v hv; simp only [Function.mem_mulSupport, ne_eq] at hv
    by_contra h; simp only [Finset.mem_coe] at h; simp [pick, h] at hv
  -- ---------------------------------------------------------------
  -- Case split on the distinguished place w.
  -- ---------------------------------------------------------------
  rcases w with w₀ | w_fin
  · -- ============================================================
    -- Case 1: w = Sum.inl w₀  (w₀ is an infinite place).
    -- Construction:
    --   • inf_comp w₀        = algebraMap K w₀.Completion n  (large, n ≫ 0)
    --   • inf_comp w' ∈ Sinf = pick_sinf w'                 (norm ≤ δ w')
    --   • inf_comp w' (else) = 1
    --   • fin_comp            = pick  (satisfies Sfin, Tfin)
    -- ============================================================
    let fin_comp : FiniteAdeleRing (𝓞 K) K :=
      ⟨pick, Filter.Eventually.of_forall h_pick_int⟩
    -- Build elements of small norm at each Sinf place.
    have h_pick_sinf : ∀ w' ∈ Sinf, ∃ e : w'.Completion, 0 < ‖e‖ ∧ ‖e‖ ≤ δ w' :=
      fun w' hw' => exists_small_norm_elem K w' (δ w') (hδ w' hw')
    let pick_sinf : ∀ w' : InfinitePlace K, w'.Completion :=
      fun w' => if hw' : w' ∈ Sinf then Classical.choose (h_pick_sinf w' hw') else 1
    have h_ps_pos : ∀ w' ∈ Sinf, 0 < ‖pick_sinf w'‖ := by
      intro w' hw'; simp only [pick_sinf, dif_pos hw']
      exact (Classical.choose_spec (h_pick_sinf w' hw')).1
    have h_ps_le : ∀ w' ∈ Sinf, ‖pick_sinf w'‖ ≤ δ w' := by
      intro w' hw'; simp only [pick_sinf, dif_pos hw']
      exact (Classical.choose_spec (h_pick_sinf w' hw')).2
    -- w₀ ∉ Sinf: every Sinf element differs from w₀ by hwSinf.
    have h_w₀_notin_Sinf : w₀ ∉ Sinf :=
      fun hw => absurd rfl (hwSinf w₀ hw)
    -- C_Sinf = ∏ w' ∈ Sinf, ‖pick_sinf w'‖^w'.mult > 0.
    let C_Sinf := ∏ w' ∈ Sinf, ‖pick_sinf w'‖ ^ w'.mult
    have h_C_Sinf_pos : 0 < C_Sinf :=
      Finset.prod_pos (fun w' hw' => pow_pos (h_ps_pos w' hw') _)
    -- Choose n so that n · C_Sfin · C_Sinf > B.
    obtain ⟨n, hn⟩ := exists_nat_gt (B / ((∏ v ∈ Sfin, ‖pick v‖) * C_Sinf))
    -- Norm of n at an infinite place.
    have h_norm_n : ‖algebraMap K w₀.Completion (n : K)‖ = (n : ℝ) := by
      rw [show algebraMap K w₀.Completion (n : K) =
          (((n : K) : WithAbs w₀.1) : w₀.Completion) from rfl,
          InfinitePlace.Completion.norm_coe]
      simp [WithAbs.equiv, InfinitePlace.map_natCast]
    -- Piecewise infinite component.
    let inf_comp : InfiniteAdeleRing K := fun w' =>
      if hw' : w' ∈ Sinf then pick_sinf w'
      else if w' = w₀ then algebraMap K w'.Completion (n : K)
      else 1
    -- The valuation mulSupport of the finite component is finite (⊆ Sfin).
    have h_z_supp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
        Valued.v ((fin_comp : FiniteAdeleRing (𝓞 K) K) v)).Finite := by
      apply Set.Finite.subset Sfin.finite_toSet
      intro v hv; simp only [Function.mem_mulSupport, ne_eq] at hv
      by_contra h; simp only [Finset.mem_coe] at h
      exact hv (show Valued.v (pick v) = 1 by simp [pick, h])
    refine ⟨(inf_comp, fin_comp), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Sfin condition.
      intro v hv; change Valued.v (pick v) ≤ ε v
      rw [h_pick_val v hv]; exact min_le_left _ _
    · -- Sinf condition: ‖inf_comp w'‖ ≤ δ w' for w' ∈ Sinf.
      intro w' hw'
      change ‖inf_comp w'‖ ≤ δ w'
      have : inf_comp w' = pick_sinf w' := dif_pos hw'
      rw [this]; exact h_ps_le w' hw'
    · -- Tfin integrality.
      intro v _; exact h_pick_int v
    · -- mulSupport ⊆ Sfin (finite).
      exact h_z_supp
    · -- ‖z‖ > B: C_Sfin · n^w₀.mult · C_Sinf > B.
      rw [norm_eq_finprod_mul_prod K (inf_comp, fin_comp) h_z_supp]
      simp_rw [show ∀ v, (fin_comp : FiniteAdeleRing (𝓞 K) K) v = pick v from fun _ => rfl]
      rw [finprod_eq_prod_of_mulSupport_subset _ h_pick_supp]
      -- Compute the infinite product.
      have h_inf_prod : ∏ w' : InfinitePlace K, ‖inf_comp w'‖ ^ w'.mult =
          (n : ℝ) ^ w₀.mult * C_Sinf := by
        -- Pull w₀ out of the full product.
        rw [← Finset.mul_prod_erase Finset.univ (fun w' => ‖inf_comp w'‖ ^ w'.mult)
              (Finset.mem_univ w₀)]
        congr 1
        · -- Factor at w₀: ‖algebraMap K w₀.Completion n‖^w₀.mult = n^w₀.mult.
          have h_w₀_val : inf_comp w₀ = algebraMap K w₀.Completion (n : K) := by
            simp only [inf_comp, dif_neg h_w₀_notin_Sinf, if_true]
          rw [h_w₀_val, h_norm_n]
        · -- Product over Finset.univ.erase w₀ equals C_Sinf.
          have h_Sinf_sub : Sinf ⊆ Finset.univ.erase w₀ := fun w' hw' =>
            Finset.mem_erase.mpr ⟨fun h => h_w₀_notin_Sinf (h ▸ hw'), Finset.mem_univ _⟩
          rw [← Finset.prod_sdiff h_Sinf_sub]
          -- The (erase w₀) \ Sinf part is all 1.
          have h_rest_one : ∏ w' ∈ (Finset.univ.erase w₀) \ Sinf,
              ‖inf_comp w'‖ ^ w'.mult = 1 := by
            apply Finset.prod_eq_one; intro w' hw'
            simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true] at hw'
            have : inf_comp w' = 1 := by
              simp only [inf_comp, dif_neg hw'.2, if_neg hw'.1]
            simp [this]
          rw [h_rest_one, one_mul]
          -- Sinf part: inf_comp w' = pick_sinf w' for w' ∈ Sinf.
          apply Finset.prod_congr rfl; intro w' hw'
          have : inf_comp w' = pick_sinf w' := dif_pos hw'
          rw [this]
      rw [h_inf_prod]
      -- Now show: C_Sfin * (n^w₀.mult * C_Sinf) > B.
      rw [div_lt_iff₀ (mul_pos h_C_pos h_C_Sinf_pos)] at hn
      have h_mult_pos : 0 < w₀.mult := InfinitePlace.mult_pos
      have h_n_le : (n : ℝ) ≤ (n : ℝ) ^ w₀.mult :=
        by exact_mod_cast Nat.le_self_pow h_mult_pos.ne' n
      calc B < (n : ℝ) * ((∏ v ∈ Sfin, ‖pick v‖) * C_Sinf) := hn
        _ = (∏ v ∈ Sfin, ‖pick v‖) * ((n : ℝ) * C_Sinf) := by ring
        _ ≤ (∏ v ∈ Sfin, ‖pick v‖) * ((n : ℝ) ^ w₀.mult * C_Sinf) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt h_C_pos)
              exact mul_le_mul_of_nonneg_right h_n_le (le_of_lt h_C_Sinf_pos)
    · -- Non-Sinf non-w₀ infinite places have norm 1.
      -- For w' ∉ Sinf and Sum.inl w' ≠ Sum.inl w₀ (i.e., w' ≠ w₀): inf_comp w' = 1.
      intro w' h_notin_Sinf h_ne
      have h_ne' : w' ≠ w₀ := fun h => h_ne (congrArg Sum.inl h)
      have : inf_comp w' = 1 := by
        simp only [inf_comp, dif_neg h_notin_Sinf, if_neg h_ne']
      simp [this]
  · -- ============================================================
    -- Case 2: w = Sum.inr w_fin  (w_fin is a finite place).
    -- Construction:
    --   • fin_comp w_fin = π₀^n     (‖π₀‖ > 1 from NontriviallyNormedField, n large)
    --   • fin_comp v = pick v       for v ∈ Sfin  (w_fin ∉ Sfin by hwSfin)
    --   • fin_comp v = 1            elsewhere
    --   • inf_comp w' = pick_sinf w' for w' ∈ Sinf  (small norm ≤ δ w')
    --   • inf_comp w' = 1           elsewhere
    -- ‖z‖ = ‖π₀‖^n · C_Sfin · C_Sinf > B for large enough n.
    -- ============================================================
    -- -------------------------------------------------------
    -- Small-norm elements at Sinf.
    -- -------------------------------------------------------
    have h_pick_sinf : ∀ w' ∈ Sinf, ∃ e : w'.Completion, 0 < ‖e‖ ∧ ‖e‖ ≤ δ w' :=
      fun w' hw' => exists_small_norm_elem K w' (δ w') (hδ w' hw')
    let pick_sinf : ∀ w' : InfinitePlace K, w'.Completion :=
      fun w' => if hw' : w' ∈ Sinf then Classical.choose (h_pick_sinf w' hw') else 1
    have h_ps_pos : ∀ w' ∈ Sinf, 0 < ‖pick_sinf w'‖ := by
      intro w' hw'; simp only [pick_sinf, dif_pos hw']
      exact (Classical.choose_spec (h_pick_sinf w' hw')).1
    have h_ps_le : ∀ w' ∈ Sinf, ‖pick_sinf w'‖ ≤ δ w' := by
      intro w' hw'; simp only [pick_sinf, dif_pos hw']
      exact (Classical.choose_spec (h_pick_sinf w' hw')).2
    let C_Sinf := ∏ w' ∈ Sinf, ‖pick_sinf w'‖ ^ w'.mult
    have h_C_Sinf_pos : 0 < C_Sinf :=
      Finset.prod_pos (fun w' hw' => pow_pos (h_ps_pos w' hw') _)
    -- -------------------------------------------------------
    -- w_fin ∉ Sfin (hwSfin) and w_fin ∉ Tfin (hwTfin).
    -- -------------------------------------------------------
    have h_wfin_notin_Sfin : w_fin ∉ Sfin :=
      fun h => absurd rfl (hwSfin w_fin h)
    have h_wfin_notin_Tfin : w_fin ∉ Tfin :=
      fun h => absurd rfl (hwTfin w_fin h)
    -- -------------------------------------------------------
    -- Get π₀ : w_fin.adicCompletion K with ‖π₀‖ > 1.
    -- -------------------------------------------------------
    letI : NontriviallyNormedField (w_fin.adicCompletion K) :=
      Valued.toNontriviallyNormedField
    obtain ⟨π₀, hπ₀⟩ := NontriviallyNormedField.non_trivial (α := w_fin.adicCompletion K)
    -- hπ₀ : 1 < ‖π₀‖
    -- -------------------------------------------------------
    -- Choose n with ‖π₀‖^n · C_Sfin · C_Sinf > B.
    -- -------------------------------------------------------
    obtain ⟨n, hn⟩ :=
      (tendsto_pow_atTop_atTop_of_one_lt hπ₀).eventually_gt_atTop
        (B / ((∏ v ∈ Sfin, ‖pick v‖) * C_Sinf)) |>.exists
    -- hn : B / ((∏ v ∈ Sfin, ‖pick v‖) * C_Sinf) < ‖π₀‖^n
    -- -------------------------------------------------------
    -- Construct the adele z = (inf_comp2, fin_comp2).
    -- -------------------------------------------------------
    let large_w : w_fin.adicCompletion K := π₀ ^ n
    let fin_comp2_fn : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K :=
      fun v => if h : v = w_fin then h ▸ large_w else if v ∈ Sfin then pick v else 1
    have h_fin_adele2 : ∀ᶠ v in Filter.cofinite,
        fin_comp2_fn v ∈ v.adicCompletionIntegers K := by
      rw [eventually_cofinite]
      apply Set.Finite.subset (Set.finite_singleton w_fin)
      intro v hv
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hv ⊢
      by_contra h_ne
      exact hv (by
        simp only [fin_comp2_fn, dif_neg h_ne]
        split_ifs with h
        · exact h_pick_int v
        · simp)
    let fin_comp2 : FiniteAdeleRing (𝓞 K) K := ⟨fin_comp2_fn, h_fin_adele2⟩
    let inf_comp2 : InfiniteAdeleRing K :=
      fun w' => if hw' : w' ∈ Sinf then pick_sinf w' else 1
    -- The valuation mulSupport of the finite component is finite (⊆ Sfin ∪ {w_fin}).
    have h_z_supp2 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
        Valued.v ((fin_comp2 : FiniteAdeleRing (𝓞 K) K) v)).Finite := by
      apply Set.Finite.subset (Finset.finite_toSet (insert w_fin Sfin))
      intro v hv; simp only [Function.mem_mulSupport] at hv
      simp only [Finset.mem_coe, Finset.mem_insert]
      by_contra h; push_neg at h
      obtain ⟨h1, h2⟩ := h
      exact hv (show Valued.v (fin_comp2_fn v) = 1 from by
        have : fin_comp2_fn v = 1 := by
          change (if h : v = w_fin then h ▸ large_w
                  else if v ∈ Sfin then pick v else (1 : v.adicCompletion K)) = 1
          rw [dif_neg h1, if_neg h2]
        rw [this, map_one])
    refine ⟨(inf_comp2, fin_comp2), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Sfin condition: Valued.v (fin_comp2 v) ≤ ε v for v ∈ Sfin.
      intro v hv; change Valued.v (fin_comp2_fn v) ≤ ε v
      have h_ne : v ≠ w_fin :=
        fun h => absurd (h ▸ rfl : (Sum.inr v : Place K) = Sum.inr w_fin) (hwSfin v hv)
      simp only [fin_comp2_fn, dif_neg h_ne, if_pos hv]
      rw [h_pick_val v hv]; exact min_le_left _ _
    · -- Sinf condition: ‖inf_comp2 w'‖ ≤ δ w' for w' ∈ Sinf.
      intro w' hw'; change ‖inf_comp2 w'‖ ≤ δ w'
      simp only [inf_comp2, dif_pos hw']; exact h_ps_le w' hw'
    · -- Tfin integrality: fin_comp2 v ∈ adicCompletionIntegers for v ∈ Tfin.
      intro v hv; change fin_comp2_fn v ∈ v.adicCompletionIntegers K
      have h_ne : v ≠ w_fin := fun h => absurd (h ▸ hv) h_wfin_notin_Tfin
      simp only [fin_comp2_fn, dif_neg h_ne]
      split_ifs with h
      · exact h_pick_int v
      · simp
    · -- mulSupport of Valued.v ∘ z.2 is finite (⊆ Sfin ∪ {w_fin}).
      exact h_z_supp2
    · -- ‖z‖ > B.
      rw [norm_eq_finprod_mul_prod K (inf_comp2, fin_comp2) h_z_supp2]
      simp_rw [show ∀ v, (fin_comp2 : FiniteAdeleRing (𝓞 K) K) v = fin_comp2_fn v from
        fun _ => rfl]
      -- Evaluate finite finprod.
      have h_fin_supp : Function.mulSupport (fun v => ‖fin_comp2_fn v‖) ⊆
          ↑(insert w_fin Sfin) := by
        intro v hv; simp only [Function.mem_mulSupport] at hv
        simp only [Finset.mem_coe, Finset.mem_insert]
        by_contra h; push_neg at h
        obtain ⟨h1, h2⟩ := h
        exact hv (show ‖fin_comp2_fn v‖ = 1 from by
          have : fin_comp2_fn v = 1 := by
            change (if h : v = w_fin then h ▸ large_w
                    else if v ∈ Sfin then pick v else (1 : v.adicCompletion K)) = 1
            rw [dif_neg h1, if_neg h2]
          rw [this, norm_one])
      rw [finprod_eq_prod_of_mulSupport_subset _ h_fin_supp,
          Finset.prod_insert h_wfin_notin_Sfin]
      -- Evaluate infinite product.
      have h_inf_prod : ∏ w' : InfinitePlace K, ‖inf_comp2 w'‖ ^ w'.mult = C_Sinf := by
        have h_rest : ∏ w' ∈ Finset.univ \ Sinf, ‖inf_comp2 w'‖ ^ w'.mult = 1 := by
          apply Finset.prod_eq_one; intro w' hw'
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hw'
          simp [inf_comp2, hw']
        have h_Sinf : ∏ w' ∈ Sinf, ‖inf_comp2 w'‖ ^ w'.mult = C_Sinf := by
          apply Finset.prod_congr rfl; intro w' hw'
          simp [inf_comp2, hw']
        calc ∏ w' : InfinitePlace K, ‖inf_comp2 w'‖ ^ w'.mult
            = (∏ w' ∈ Finset.univ \ Sinf, ‖inf_comp2 w'‖ ^ w'.mult) *
              ∏ w' ∈ Sinf, ‖inf_comp2 w'‖ ^ w'.mult :=
                (Finset.prod_sdiff (Finset.subset_univ Sinf)).symm
          _ = 1 * C_Sinf := by rw [h_rest, h_Sinf]
          _ = C_Sinf := one_mul _
      rw [h_inf_prod]
      -- Simplify factors.
      have h_w_val : ‖fin_comp2_fn w_fin‖ = ‖π₀‖ ^ n := by
        simp [fin_comp2_fn, dif_pos rfl, large_w, norm_pow]
      have h_sfin_eq : ∏ v ∈ Sfin, ‖fin_comp2_fn v‖ = ∏ v ∈ Sfin, ‖pick v‖ := by
        apply Finset.prod_congr rfl; intro v hv
        have h_ne : v ≠ w_fin := fun h => absurd (h ▸ hv) h_wfin_notin_Sfin
        simp only [fin_comp2_fn, dif_neg h_ne, if_pos hv]
      rw [h_w_val, h_sfin_eq]
      -- Use hn to get the inequality.
      have hn' : B < ‖π₀‖ ^ n * ((∏ v ∈ Sfin, ‖pick v‖) * C_Sinf) :=
        (div_lt_iff₀ (mul_pos h_C_pos h_C_Sinf_pos)).mp hn
      calc B < ‖π₀‖ ^ n * ((∏ v ∈ Sfin, ‖pick v‖) * C_Sinf) := hn'
        _ = (‖π₀‖ ^ n * ∏ v ∈ Sfin, ‖pick v‖) * C_Sinf := by ring
    · -- 6th output: Sum.inl w' ≠ Sum.inr w_fin always, so ‖inf_comp2 w'‖ ≤ 1
      -- for all w' ∉ Sinf (since inf_comp2 w' = 1 there).
      intro w' h_notin_Sinf _
      simp only [inf_comp2, dif_neg h_notin_Sinf, norm_one, le_refl]

/-! ### Cocompactness: a compact set covering 𝔸_K modulo K

The deep input is `NumberField.AdeleRing.cocompact` from the FLT package:
the quotient `𝔸_K ⧸ K` is compact (Neukirch ANT §II.25, Theorem 25.12; proved in FLT
by base change from the explicit fundamental domain for ℚ).

From this we extract a **compact** set `W₀ ⊆ 𝔸_K` with `K + W₀ = 𝔸_K`.
Note: the naive set `W = {integral at finite places, ‖·‖ ≤ 1 at infinite places}`
does *not* work for general K — the covering radius of the lattice 𝓞_K in
∏_w K_w can exceed 1 (e.g. for imaginary quadratic fields of large discriminant).
Instead, the local bounds satisfied by the compact W₀ (uniform valuation bounds,
integrality at almost all finite places) are extracted in `isCompact_finAdele_bounds`
and `isCompact_infAdele_bounds` below and absorbed into the ε/δ bookkeeping
of `strong_approximation`. -/

/-- **Compact covering of 𝔸_K mod K** (from FLT's `NumberField.AdeleRing.cocompact`).
    There is a compact set W₀ such that every adele c decomposes as c = diag a + b
    with a ∈ K and b ∈ W₀. -/
lemma exists_compact_cover :
    ∃ W₀ : Set (𝔸 K), IsCompact W₀ ∧
      ∀ c : 𝔸 K, ∃ (a : K) (b : 𝔸 K), b ∈ W₀ ∧ c = diag K a + b := by
  haveI := NumberField.AdeleRing.cocompact K
  -- Choose a compact neighborhood C x of each point x.
  have h_nbhd : ∀ x : 𝔸 K, ∃ C : Set (𝔸 K), IsCompact C ∧ C ∈ 𝓝 x :=
    fun x => exists_compact_mem_nhds x
  choose C hC_comp hC_nhds using h_nbhd
  -- The images of their interiors under the quotient map are open and cover the quotient.
  set N := NumberField.AdeleRing.principalSubgroup (𝓞 K) K
  have h_open : ∀ x : 𝔸 K,
      IsOpen ((QuotientAddGroup.mk : (𝔸 K) → (𝔸 K) ⧸ N) '' interior (C x)) :=
    fun x => QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap _ isOpen_interior
  have h_cover : (Set.univ : Set ((𝔸 K) ⧸ N)) ⊆
      ⋃ x : 𝔸 K, (QuotientAddGroup.mk : (𝔸 K) → (𝔸 K) ⧸ N) '' interior (C x) := by
    intro q _
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact Set.mem_iUnion.mpr ⟨x, ⟨x, mem_interior_iff_mem_nhds.mpr (hC_nhds x), rfl⟩⟩
  -- Extract a finite subcover.
  obtain ⟨t, ht⟩ := CompactSpace.isCompact_univ.elim_finite_subcover _ h_open h_cover
  refine ⟨⋃ x ∈ t, C x, t.isCompact_biUnion (fun x _ => hC_comp x), fun c => ?_⟩
  -- Decompose an arbitrary adele c.
  have hc : (QuotientAddGroup.mk c : (𝔸 K) ⧸ N) ∈
      ⋃ x ∈ t, (QuotientAddGroup.mk : (𝔸 K) → (𝔸 K) ⧸ N) '' interior (C x) :=
    ht (Set.mem_univ _)
  obtain ⟨x, hx_t, b, hb_int, hπ⟩ := Set.mem_iUnion₂.mp hc
  -- (b : quotient) = (c : quotient) ⇒ c - b ∈ N = principal adeles.
  have h_mem : c - b ∈ N := by
    rw [← QuotientAddGroup.eq_iff_sub_mem]
    exact hπ.symm
  obtain ⟨a, ha⟩ := h_mem
  exact ⟨a, b, Set.mem_biUnion hx_t (interior_subset hb_int),
    by rw [show diag K a = c - b from ha]; ring⟩

/-- **Valuation bounds on a compact set of finite adeles.**
    A compact set of finite adeles admits a uniform valuation bound `C v` at every
    finite place, with `C v = 1` for all but finitely many `v`.
    Proof: cover by finitely many translates `a + Ô` of the (open) integral adeles;
    the ultrametric inequality bounds each coordinate by `max (Valued.v (a v)) 1`. -/
lemma isCompact_finAdele_bounds {Wf : Set (FiniteAdeleRing (𝓞 K) K)} (hWf : IsCompact Wf) :
    ∃ C : HeightOneSpectrum (𝓞 K) → ℤᵐ⁰,
      (∀ v, 1 ≤ C v) ∧ (∀ᶠ v in Filter.cofinite, C v = 1) ∧
      ∀ b ∈ Wf, ∀ v, Valued.v (b v) ≤ C v := by
  -- The integral adeles form an open set.
  have h_int_open : IsOpen {x : FiniteAdeleRing (𝓞 K) K |
      ∀ v, x v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_integer _
  -- Cover Wf by the translates a + Ô.
  set U : FiniteAdeleRing (𝓞 K) K → Set (FiniteAdeleRing (𝓞 K) K) :=
    fun a => {b | ∀ v, (b - a) v ∈ v.adicCompletionIntegers K} with hU_def
  have hU_nhds : ∀ a ∈ Wf, U a ∈ 𝓝 a := by
    intro a _
    have h_preim : U a =
        (fun b => b - a) ⁻¹' {x | ∀ v, x v ∈ v.adicCompletionIntegers K} := rfl
    rw [h_preim]
    apply (h_int_open.preimage (continuous_id.sub continuous_const)).mem_nhds
    simp only [Set.mem_preimage, Set.mem_setOf_eq, id_eq]
    intro v
    rw [sub_self]
    change (0 : v.adicCompletion K) ∈ _
    exact zero_mem _
  obtain ⟨t, ht_sub, ht_cover⟩ := hWf.elim_nhds_subcover U hU_nhds
  refine ⟨fun v => (t.sup fun a => Valued.v (a v)) ⊔ 1, fun v => le_sup_right, ?_, ?_⟩
  · -- C v = 1 for cofinitely many v: each a ∈ t is integral at cofinitely many v.
    have h_ev : ∀ᶠ v in Filter.cofinite, ∀ a ∈ t, Valued.v (a v) ≤ 1 := by
      rw [Filter.eventually_all_finset]
      intro a _
      filter_upwards [a.2] with v hv
      rwa [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hv
    filter_upwards [h_ev] with v hv
    rw [sup_eq_right]
    exact Finset.sup_le hv
  · -- The bound: b = (b - a) + a with b - a integral and a ∈ t.
    intro b hb v
    obtain ⟨a, ha_t, hba⟩ := Set.mem_iUnion₂.mp (ht_cover hb)
    have h1 : Valued.v ((b - a) v) ≤ 1 := by
      have h := hba v
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    have h2 : Valued.v (a v) ≤ t.sup fun a => Valued.v (a v) :=
      Finset.le_sup (f := fun a => Valued.v (a v)) ha_t
    have hb_eq : b v = (b - a) v + a v := by
      change b v = (b v - a v) + a v
      ring
    rw [hb_eq]
    calc Valued.v ((b - a) v + a v)
        ≤ max (Valued.v ((b - a) v)) (Valued.v (a v)) := map_add_le_max _ _ _
      _ ≤ (t.sup fun a => Valued.v (a v)) ⊔ 1 :=
          max_le (le_sup_of_le_right h1) (le_sup_of_le_left h2)

/-- **Norm bounds on a compact set of infinite adeles.**
    A compact set of infinite adeles admits a uniform norm bound (≥ 1)
    valid at every infinite place. -/
lemma isCompact_infAdele_bounds {Wi : Set (InfiniteAdeleRing K)} (hWi : IsCompact Wi) :
    ∃ Cinf : ℝ, 1 ≤ Cinf ∧ ∀ b ∈ Wi, ∀ w : InfinitePlace K, ‖b w‖ ≤ Cinf := by
  -- At each place, evaluation is continuous, so the norm is bounded on the compact Wi.
  have h_bd : ∀ w : InfinitePlace K, ∃ Cw : ℝ, ∀ b ∈ Wi, ‖b w‖ ≤ Cw := fun w =>
    hWi.exists_bound_of_continuousOn (continuous_apply w).continuousOn
  choose Cw hCw using h_bd
  refine ⟨1 + ∑ w : InfinitePlace K, max (Cw w) 0, ?_, ?_⟩
  · have h_sum : 0 ≤ ∑ w : InfinitePlace K, max (Cw w) 0 :=
      Finset.sum_nonneg fun w _ => le_max_right _ _
    linarith
  · intro b hb w
    calc ‖b w‖ ≤ Cw w := hCw w b hb
      _ ≤ max (Cw w) 0 := le_max_left _ _
      _ ≤ ∑ w' : InfinitePlace K, max (Cw w') 0 :=
          Finset.single_le_sum (fun w' _ => le_max_right _ _) (Finset.mem_univ w)
      _ ≤ 1 + ∑ w' : InfinitePlace K, max (Cw w') 0 := by linarith

/-- **Packaged covering data** for the strong approximation proof:
    a set W₀ with `K + W₀ = 𝔸_K` together with uniform local bounds
    (valuation bound `Cfin v` at finite places, `= 1` almost everywhere;
    norm bound `Cinf` at infinite places).
    This replaces the classical "fundamental domain W" of Neukirch §II.25:
    for general K the naive unit-ball W does not cover 𝔸_K mod K, but a compact
    covering set always exists, and compactness yields the local bounds. -/
lemma exists_cover_with_bounds :
    ∃ (W₀ : Set (𝔸 K)) (Cfin : HeightOneSpectrum (𝓞 K) → ℤᵐ⁰) (Cinf : ℝ),
      (∀ c : 𝔸 K, ∃ (a : K) (b : 𝔸 K), b ∈ W₀ ∧ c = diag K a + b) ∧
      (∀ v, 1 ≤ Cfin v) ∧ (∀ᶠ v in Filter.cofinite, Cfin v = 1) ∧ (1 ≤ Cinf) ∧
      (∀ b ∈ W₀, ∀ v, Valued.v ((b : 𝔸 K).2 v) ≤ Cfin v) ∧
      (∀ b ∈ W₀, ∀ w : InfinitePlace K, ‖(b : 𝔸 K).1 w‖ ≤ Cinf) := by
  obtain ⟨W₀, hW₀_comp, hW₀_cover⟩ := exists_compact_cover K
  obtain ⟨Cfin, hCfin_one, hCfin_ev, hCfin_bd⟩ :=
    isCompact_finAdele_bounds K (hW₀_comp.image continuous_snd)
  obtain ⟨Cinf, hCinf_one, hCinf_bd⟩ :=
    isCompact_infAdele_bounds K (hW₀_comp.image continuous_fst)
  exact ⟨W₀, Cfin, Cinf, hW₀_cover, hCfin_one, hCfin_ev, hCinf_one,
    fun b hb v => hCfin_bd _ (Set.mem_image_of_mem _ hb) v,
    fun b hb w => hCinf_bd _ (Set.mem_image_of_mem _ hb) w⟩

/-- For nonzero u ∈ K×, the scaled covering: every adele c decomposes as
    c = diag(a) + diag(u)·b with a ∈ K, b ∈ W₀.
    Proof: apply the covering to u⁻¹·c, then multiply through by u. -/
lemma exists_cover_smul (W₀ : Set (𝔸 K))
    (hW₀ : ∀ c : 𝔸 K, ∃ (a : K) (b : 𝔸 K), b ∈ W₀ ∧ c = diag K a + b)
    (u : K) (hu : u ≠ 0) (c : 𝔸 K) :
    ∃ (a : K) (b : 𝔸 K), b ∈ W₀ ∧ c = diag K a + diag K u * b := by
  obtain ⟨a, b, hb, hab⟩ := hW₀ (diag K u⁻¹ * c)
  refine ⟨u * a, b, hb, ?_⟩
  have hmul : diag K u * (diag K u⁻¹ * c) = c := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hu, map_one, one_mul]
  calc c = diag K u * (diag K u⁻¹ * c)        := hmul.symm
       _ = diag K u * (diag K a + b)          := by rw [hab]
       _ = diag K u * diag K a + diag K u * b := by ring
       _ = diag K (u * a) + diag K u * b      := by rw [← map_mul]

/-! ### Main theorem: Strong Approximation -/

/-- **Strong Approximation Theorem** (Theorem 25.16, full statement).

    Let K be a number field. Let `w : Place K` be the unique **unconstrained** place.
    Let M_K = Sfin ⊔ Sinf ⊔ Tfin ⊔ {w} be a partition of the relevant places:
    - Sfin (finite, finite-place approximation): Valued.v((x - target)_v) ≤ ε_v
    - Sinf (finite, infinite-place approximation): ‖(x - target)_{w'}‖ ≤ δ_{w'}
    - Tfin (possibly infinite, finite-place integrality): (diag x)_v ∈ O_v
    - Tinf (possibly infinite, infinite-place integrality): ‖(diag x)_{w'}‖ ≤ 1
    - {w} (one place, finite or infinite): unconstrained

    Hypotheses for Tinf: target.1 w' = 0 at Tinf places (needed for the coset-decomposition
    proof; this is the analogue of target.2 v ∈ O_v for finite Tfin places).

    ### Proof structure (sorry-free; deep inputs: Minkowski via Mathlib,
    cocompactness via FLT)
    0. `exists_cover_with_bounds` (from FLT's `NumberField.AdeleRing.cocompact`)
       gives a covering set W₀ with local bounds Cfin v (= 1 a.e.) and Cinf.
    1. Blichfeldt-Minkowski gives B > 0.
    2. `exists_adele_large_norm` builds z for the *enlarged* sets
       Sfin' = Sfin ∪ {bad Tfin places}, Sinf' = Sinf ∪ Tinf with *shrunken*
       tolerances ε' = ε/Cfin resp. (Cfin)⁻¹, δ' = δ/Cinf resp. 1/Cinf.
    3. BM gives u ∈ K× with |u|_v ≤ |z|_v (finite) and ‖u_{w'}‖ ≤ ‖z.1 w'‖ (infinite).
    4. Coset decomposition: target = diag x + diag u · b with b ∈ W₀ (`exists_cover_smul`).
    5. The covering constants cancel:
       Sfin: |(x-target)_v| = |(ub)_v| ≤ |z_v|·Cfin v ≤ (ε_v/Cfin v)·Cfin v = ε_v.
       Sinf: ‖(x-target)_{w'}‖ ≤ ‖z.1 w'‖·Cinf ≤ (δ_{w'}/Cinf)·Cinf = δ_{w'}.
       Tfin: |(ub)_v| ≤ (Cfin v)⁻¹·Cfin v = 1, so diag x = target - ub is integral.
       Tinf: ‖(diag x)_{w'}‖ = ‖(ub)_{w'}‖ ≤ (1/Cinf)·Cinf = 1 (since target.1 w' = 0). -/
theorem strong_approximation
    (w : Place K)
    (Sfin : Finset (HeightOneSpectrum (𝓞 K)))
    (Sinf : Finset (InfinitePlace K))
    (Tfin : Set (HeightOneSpectrum (𝓞 K)))
    (Tinf : Set (InfinitePlace K))
    -- disjointness
    (hSfinTfin : ∀ v, v ∈ Sfin → v ∉ Tfin)
    (hSinfTinf : ∀ w', w' ∈ Sinf → w' ∉ Tinf)
    -- w is not in S or T
    (hwSfin : ∀ v ∈ Sfin, (Sum.inr v : Place K) ≠ w)
    (hwSinf : ∀ w' ∈ Sinf, (Sum.inl w' : Place K) ≠ w)
    (hwTfin : ∀ v ∈ Tfin, (Sum.inr v : Place K) ≠ w)
    (hwTinf : ∀ w' ∈ Tinf, (Sum.inl w' : Place K) ≠ w)
    -- coverage: every place is in S, T, or {w}
    (hcover_fin : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sfin ∨ v ∈ Tfin ∨ (Sum.inr v : Place K) = w)
    (hcover_inf : ∀ w' : InfinitePlace K, w' ∈ Sinf ∨ w' ∈ Tinf ∨ (Sum.inl w' : Place K) = w)
    -- target adele
    (target : 𝔸 K)
    (hTfin_target : ∀ v ∈ Tfin, target.2 v ∈ v.adicCompletionIntegers K)
    (hTinf_target : ∀ w' ∈ Tinf, target.1 w' = 0)
    -- approximation tolerance
    (ε : HeightOneSpectrum (𝓞 K) → ℤᵐ⁰)
    (hε : ∀ v ∈ Sfin, (0 : ℤᵐ⁰) < ε v)
    (δ : InfinitePlace K → ℝ)
    (hδ : ∀ w' ∈ Sinf, 0 < δ w') :
    ∃ x : K,
      (∀ v ∈ Sfin, Valued.v ((diag K x - target).2 v) ≤ ε v) ∧
      (∀ w' ∈ Sinf, ‖(diag K x - target).1 w'‖ ≤ δ w') ∧
      (∀ v ∈ Tfin, (diag K x).2 v ∈ v.adicCompletionIntegers K) ∧
      (∀ w' ∈ Tinf, ‖(diag K x).1 w'‖ ≤ 1) := by
  -- ----------------------------------------------------------------
  -- Step 0. Covering data W₀, Cfin, Cinf from cocompactness (FLT).
  -- ----------------------------------------------------------------
  obtain ⟨W₀, Cfin, Cinf, hW₀_cover, hCfin_one, hCfin_ev, hCinf_one, hCfin_bd, hCinf_bd⟩ :=
    exists_cover_with_bounds K
  have hCinf_pos : (0 : ℝ) < Cinf := lt_of_lt_of_le one_pos hCinf_one
  have hCfin_ne : ∀ v, Cfin v ≠ 0 := fun v =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (hCfin_one v))
  -- Sbad: the finitely many finite places where Cfin v ≠ 1.
  set Sbad : Finset (HeightOneSpectrum (𝓞 K)) :=
    (Filter.eventually_cofinite.mp hCfin_ev).toFinset with hSbad_def
  have hSbad_one : ∀ v, v ∉ Sbad → Cfin v = 1 := by
    intro v hv
    by_contra h
    exact hv ((Filter.eventually_cofinite.mp hCfin_ev).mem_toFinset.mpr h)
  -- ----------------------------------------------------------------
  -- Step 1. Extract BM constant B.
  -- ----------------------------------------------------------------
  obtain ⟨B, _B_pos, hBM⟩ := blichfeldt_minkowski K
  -- ----------------------------------------------------------------
  -- Step 2. Build z for the enlarged sets with shrunken tolerances.
  --         Sfin' adds the bad Tfin places; Sinf' adds all Tinf places.
  -- ----------------------------------------------------------------
  have hwSfin' : ∀ v ∈ Sfin ∪ Sbad.filter (· ∈ Tfin), (Sum.inr v : Place K) ≠ w := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact hwSfin v h
    · exact hwTfin v (Finset.mem_filter.mp h).2
  have hwSinf' : ∀ w' ∈ Sinf ∪ (Set.toFinite Tinf).toFinset, (Sum.inl w' : Place K) ≠ w := by
    intro w' hw'
    rcases Finset.mem_union.mp hw' with h | h
    · exact hwSinf w' h
    · exact hwTinf w' ((Set.toFinite Tinf).mem_toFinset.mp h)
  have hε' : ∀ v ∈ Sfin ∪ Sbad.filter (· ∈ Tfin),
      (0 : ℤᵐ⁰) < (if v ∈ Sfin then ε v / Cfin v else (Cfin v)⁻¹) := by
    intro v _
    by_cases h : v ∈ Sfin
    · rw [if_pos h, zero_lt_iff]
      exact div_ne_zero (ne_of_gt (hε v h)) (hCfin_ne v)
    · rw [if_neg h, zero_lt_iff]
      exact inv_ne_zero (hCfin_ne v)
  have hδ' : ∀ w' ∈ Sinf ∪ (Set.toFinite Tinf).toFinset,
      (0 : ℝ) < (if w' ∈ Sinf then δ w' / Cinf else 1 / Cinf) := by
    intro w' _
    by_cases h : w' ∈ Sinf
    · rw [if_pos h]; exact div_pos (hδ w' h) hCinf_pos
    · rw [if_neg h]; exact div_pos one_pos hCinf_pos
  obtain ⟨z, hz_Sfin, hz_Sinf, hz_Tfin, hz_fin, hz_large, _⟩ :=
    exists_adele_large_norm K B w
      (Sfin ∪ Sbad.filter (· ∈ Tfin))
      (Sinf ∪ (Set.toFinite Tinf).toFinset)
      Tfin hwSfin' hwSinf' hwTfin
      (fun v => if v ∈ Sfin then ε v / Cfin v else (Cfin v)⁻¹) hε'
      (fun w' => if w' ∈ Sinf then δ w' / Cinf else 1 / Cinf) hδ'
  -- ----------------------------------------------------------------
  -- Step 3. Apply BM to z: get u ∈ K× with |u|_v ≤ |z|_v for all v.
  -- ----------------------------------------------------------------
  obtain ⟨u, hu_ne, hu_fin, hu_inf⟩ := hBM z hz_fin hz_large
  -- ----------------------------------------------------------------
  -- Step 4. Coset decomposition: target = diag(x) + diag(u)·b, b ∈ W₀.
  -- ----------------------------------------------------------------
  obtain ⟨x, b, hb_mem, hxb⟩ := exists_cover_smul K W₀ hW₀_cover u hu_ne target
  -- diag x - target = -(diag u * b)  [used in all four conditions]
  have hdiff : diag K x - target = -(diag K u * b) := by rw [hxb]; ring
  -- Key integrality estimate at Tfin places: |u_v · b_v| ≤ 1.
  have h_ub_int : ∀ v ∈ Tfin, Valued.v ((diag K u).2 v * b.2 v) ≤ 1 := by
    intro v hv
    have hz_le : Valued.v (z.2 v) ≤ (Cfin v)⁻¹ := by
      by_cases hbad : v ∈ Sbad
      · -- v lies in the enlarged Sfin'; the tolerance there is (Cfin v)⁻¹.
        have hv_Sfin' : v ∈ Sfin ∪ Sbad.filter (· ∈ Tfin) :=
          Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbad, hv⟩)
        have h_not_Sfin : v ∉ Sfin := fun h => hSfinTfin v h hv
        have h := hz_Sfin v hv_Sfin'
        simpa only [if_neg h_not_Sfin] using h
      · -- Cfin v = 1, and z is integral at Tfin places.
        rw [hSbad_one v hbad, inv_one]
        have h := hz_Tfin v hv
        rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    calc Valued.v ((diag K u).2 v * b.2 v)
        = Valued.v ((diag K u).2 v) * Valued.v (b.2 v) := Valuation.map_mul _ _ _
      _ ≤ Valued.v (z.2 v) * Cfin v := mul_le_mul' (hu_fin v) (hCfin_bd b hb_mem v)
      _ ≤ (Cfin v)⁻¹ * Cfin v := mul_le_mul_left hz_le _
      _ = 1 := inv_mul_cancel₀ (hCfin_ne v)
  -- ----------------------------------------------------------------
  -- Step 5. Verify the four conclusions.
  -- ----------------------------------------------------------------
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · -- Sfin: |(diag x - target)_v| = |u_v|·|b_v| ≤ |z_v|·Cfin v ≤ (ε_v/Cfin v)·Cfin v = ε_v
    intro v hv
    rw [hdiff, show (-(diag K u * b)).2 v =
        -((diag K u).2 v * b.2 v) from rfl, Valuation.map_neg, Valuation.map_mul]
    have hz_le : Valued.v (z.2 v) ≤ ε v / Cfin v := by
      have h := hz_Sfin v (Finset.mem_union_left _ hv)
      simpa only [if_pos hv] using h
    calc Valued.v ((diag K u).2 v) * Valued.v (b.2 v)
        ≤ Valued.v (z.2 v) * Cfin v := mul_le_mul' (hu_fin v) (hCfin_bd b hb_mem v)
      _ ≤ (ε v / Cfin v) * Cfin v := mul_le_mul_left hz_le _
      _ = ε v := div_mul_cancel₀ _ (hCfin_ne v)
  · -- Sinf: ‖(diag x - target)_{w'}‖ ≤ ‖z.1 w'‖·Cinf ≤ (δ_{w'}/Cinf)·Cinf = δ_{w'}
    intro w' hw'
    rw [hdiff, show (-(diag K u * b)).1 w' =
        -((diag K u).1 w' * b.1 w') from rfl, norm_neg, norm_mul]
    have hz_le : ‖z.1 w'‖ ≤ δ w' / Cinf := by
      have h := hz_Sinf w' (Finset.mem_union_left _ hw')
      simpa only [if_pos hw'] using h
    calc ‖(diag K u).1 w'‖ * ‖b.1 w'‖
        ≤ ‖z.1 w'‖ * Cinf :=
          mul_le_mul (hu_inf w') (hCinf_bd b hb_mem w') (norm_nonneg _) (norm_nonneg _)
      _ ≤ (δ w' / Cinf) * Cinf := mul_le_mul_of_nonneg_right hz_le (le_of_lt hCinf_pos)
      _ = δ w' := div_mul_cancel₀ _ (ne_of_gt hCinf_pos)
  · -- Tfin: diag(x)_v = target_v - (u·b)_v; both integral → difference integral.
    intro v hv
    have hdiag : (diag K x).2 v = target.2 v - (diag K u * b).2 v := by
      have h : diag K x = target - diag K u * b := by rw [hxb]; ring
      simp only [h, sub_eq_add_neg]; rfl
    rw [hdiag]
    apply sub_mem (hTfin_target v hv)
    rw [show (diag K u * b).2 v = (diag K u).2 v * b.2 v from rfl,
        HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h_ub_int v hv
  · -- Tinf: w' lies in the enlarged Sinf', whose tolerance 1/Cinf cancels Cinf.
    intro w' hw'
    have h_w'_notin_Sinf : w' ∉ Sinf := fun hs => hSinfTinf w' hs hw'
    have hz_le : ‖z.1 w'‖ ≤ 1 / Cinf := by
      have h := hz_Sinf w'
        (Finset.mem_union_right _ ((Set.toFinite Tinf).mem_toFinset.mpr hw'))
      simpa only [if_neg h_w'_notin_Sinf] using h
    -- (diag x).1 w' = -(u_{w'} · b_{w'})  since target.1 w' = 0
    have h_diag_x : (diag K x).1 w' = -((diag K u).1 w' * b.1 w') := by
      have h : diag K x = target - diag K u * b := by rw [hxb]; ring
      have h' : (diag K x).1 w' =
          target.1 w' - (diag K u).1 w' * b.1 w' := by rw [h]; rfl
      rw [h', hTinf_target w' hw', zero_sub]
    rw [h_diag_x, norm_neg, norm_mul]
    calc ‖(diag K u).1 w'‖ * ‖b.1 w'‖
        ≤ ‖z.1 w'‖ * Cinf :=
          mul_le_mul (hu_inf w') (hCinf_bd b hb_mem w') (norm_nonneg _) (norm_nonneg _)
      _ ≤ (1 / Cinf) * Cinf := mul_le_mul_of_nonneg_right hz_le (le_of_lt hCinf_pos)
      _ = 1 := div_mul_cancel₀ _ (ne_of_gt hCinf_pos)

end
end StrongApproximation
