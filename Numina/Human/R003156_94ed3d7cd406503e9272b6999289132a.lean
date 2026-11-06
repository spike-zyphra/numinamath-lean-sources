import Mathlib
open Finset Set Nat Polynomial
noncomputable section

-- Define the property of a polynomial with coefficients $±1$.
def is_sign_poly (n : ℕ) (p : Polynomial ℝ) : Prop :=
  p.degree = n ∧ ∀ i : ℕ, i ≤ n → p.coeff i = 1 ∨ p.coeff i = -1

-- prove $t^3 * (2 - t)$ is decreasing when $t$ ge $3/2$.
lemma monotone_decreasing (x y : ℝ) (hx : 3/2 ≤ x) (hxy : x ≤ y) :
    x^3 * (2 - x) ≥ y^3 * (2 - y) := by
  -- Define $f(t) = t^3 * (2 - t)$, the function to prove decreasing.
  let f (t : ℝ) := t^3 * (2 - t)
  let g (t : ℝ) := -f t
  let D := Set.Ici (3/2 :ℝ )
  have hD_convex : Convex ℝ D := convex_Ici (3/2)
  have hD_interior : interior D = Set.Ioi (3/2) := interior_Ici
  have h_cont_g : ContinuousOn g D := by
    simp [g, f]
    apply ContinuousOn.neg
    apply ContinuousOn.mul
    · apply ContinuousOn.pow continuousOn_id 3
    · apply ContinuousOn.sub continuousOn_const continuousOn_id
  have h_diff_g : DifferentiableOn ℝ g (interior D) := by
    simp only [g, f, hD_interior]
    apply DifferentiableOn.neg
    apply DifferentiableOn.mul
    · apply DifferentiableOn.pow differentiableOn_id
    · apply DifferentiableOn.sub
      · apply differentiableOn_const
      · apply differentiableOn_id
  have h_deriv_g_nonneg : ∀ t ∈ interior D, 0 ≤ deriv g t := by
    simp [g, f, hD_interior]
    intro t h_t
    -- Compute the derivative of $f(t)$ to show it is non-positive.
    have h_deriv_f : deriv f t = t^2 * (6 - 4 * t) := by
      simp only [f]
      have h_diff_f1 : DifferentiableAt ℝ (fun t ↦ t^3) t := by apply differentiableAt_pow
      have h_diff_f2 : DifferentiableAt ℝ (fun t ↦ 2 - t) t := by
        apply DifferentiableAt.sub
        · apply differentiableAt_const
        · apply differentiableAt_id
      have h_diff_f3 : DifferentiableAt ℝ (fun t ↦ (2: ℝ)) t := by apply differentiableAt_const
      have h_diff_f4 : DifferentiableAt ℝ (fun t ↦ t) t := by apply differentiableAt_id
      have h_diff_f : DifferentiableAt ℝ (fun t ↦ t^3 * (2 - t)) t := by
        apply DifferentiableAt.mul h_diff_f1 h_diff_f2
      rw [deriv_mul h_diff_f1 h_diff_f2]
      rw [deriv_pow, deriv_sub h_diff_f3 h_diff_f4, deriv_const, deriv_id'']
      norm_num
      ring_nf
    rw [h_deriv_f]
    have : 6 - 4 * t = 4 * (3/2 - t) := by ring
    rw [this]
    nlinarith
  -- Prove $g$ is non-strictly increasing to imply $f$ is non-strictly decreasing.
  have h_monotone_g : MonotoneOn g D := by
    apply monotoneOn_of_deriv_nonneg hD_convex h_cont_g h_diff_g h_deriv_g_nonneg
  simp [MonotoneOn, g, f] at h_monotone_g
  have h_y_in_D : y ∈ D := by simp [D, Set.Ici]; linarith
  exact h_monotone_g hx h_y_in_D hxy

/-3. [15] Let $p(x)=a_{n} x^{n}+a_{n-1} x^{n-1}+\ldots+a_{0}$, where each $a_{i}$ is either 1 or -1 . Let $r$ be a root of $p$. If $|r|>\frac{15}{8}$, what is the minimum possible value of $n$ ?-/
theorem number_theory_600999 :
  IsLeast {n : ℕ | ∃ (p : Polynomial ℝ) (r : ℝ), is_sign_poly n p ∧ p.eval r = 0 ∧ |r| > 15 / 8} 4 := by
  constructor
  -- Show there exists $n = 4$ satisfying the condition.
  · let p : Polynomial ℝ := Polynomial.X^4 - Polynomial.X^3 - Polynomial.X^2 - Polynomial.X - 1
    have h_deg : p.degree = 4 := by
      unfold p
      norm_num [is_sign_poly, Polynomial.degree_X_pow, Polynomial.degree_sub_eq_left_of_degree_lt,
          Polynomial.degree_X, Polynomial.degree_one, Polynomial.degree_neg, Polynomial.degree_add_eq_left_of_degree_lt]
    have h_coeff : ∀ i ≤ 4, p.coeff i = 1 ∨ p.coeff i = -1 := by
      intro i hi
      norm_num [is_sign_poly, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X,
        Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_neg] at hi ⊢
      rcases i with (_ | _ | _ | _ | _ | i) <;>
      norm_num [Nat.succ_le_succ_iff, Nat.succ_le_iff, Nat.zero_le] at hi ⊢ <;>
      (try ring_nf at hi ⊢) <;>
      (try norm_num at hi ⊢) <;>
      (try simp_all [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_neg])
    have h_sign : is_sign_poly 4 p := by exact ⟨h_deg, h_coeff⟩
    -- Check $p(15/8) < 0$ and $p(2) > 0$.
    have h158 : p.eval (15 / 8 : ℝ) < 0 := by
      unfold p
      norm_num
    have h2 : p.eval 2 > 0 := by
      unfold p
      norm_num
    have h_cont : ContinuousOn (fun x => p.eval x) (Set.Icc (15/8) 2) := by
      apply Polynomial.continuousOn
    have h_iv : ∃ r ∈ Set.Icc (15/8) 2, p.eval r = 0 := by
      apply intermediate_value_Icc
      · norm_num
      · exact h_cont
      · constructor
        · nlinarith
        · nlinarith
    rcases h_iv with ⟨r, hr, h_root⟩
    use p,r
    constructor
    · exact h_sign
    · have : r ≥ 15/8 := hr.1
      have h_r_nonneg : 0 ≤ r := by linarith [this]
      have h_r_gt : r > 15/8 := by
        by_contra h_not_gt
        have h_r_eq : r = 15/8 := by linarith [this, h_not_gt]
        rw [h_r_eq] at h_root
        have : p.eval (15/8) < 0 := h158
        linarith [h_root]
      rw [abs_of_nonneg h_r_nonneg]
      exact ⟨h_root,h_r_gt⟩

  -- Show $n ≤ 3$ is impossible.
  · intro n hn
    -- Proof by contradiction: Assume $n ≤ 3$, derive a contradiction.
    by_contra h_n_le_3
    have h_n : n ≤ 3 := by nlinarith
    rcases hn with ⟨p, r, h_sign, h_root, h_r⟩
    have h_deg : p.degree = n := h_sign.1
    have h_coeff : ∀ i : ℕ, i ≤ n → p.coeff i = 1 ∨ p.coeff i = -1 := h_sign.2
    have h_r_gt : |r| > 15/8 := h_r
    -- Triangle inequality.
    have h_triangle_inequality : |r|^n ≤ (|r|^n - 1) / (|r| - 1) := by
      have h_eq : |p.coeff n * r^n| = |∑ i ∈  Finset.range n, p.coeff i * r^i| := by
        have : p.eval r = 0 := h_root
        have h_eval : ∑ i ∈ Finset.range (n + 1), p.coeff i * r^i = 0 := by
          have h_eval_def : p.eval r = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * r^i := by
            simp only [Polynomial.eval, eval₂]
            apply Finset.sum_subset
            · intro i hi
              simp only [mem_support_iff] at hi
              apply Finset.mem_range.mpr
              exact lt_of_not_ge (fun h ↦ hi (Polynomial.coeff_eq_zero_of_natDegree_lt (by nlinarith)))
            · intro i hi h_i_notin
              simp only [mem_support_iff, not_not] at h_i_notin
              simp [h_i_notin]
          have h_p_nonzero : p ≠ 0 := by
              intro h_p_zero
              have : p.coeff n = 0 := by simp [h_p_zero]
              have : p.coeff n = 1 ∨ p.coeff n = -1 := h_coeff n le_rfl
              cases this
              · linarith
              · linarith
          have h_deg : p.natDegree = n := by
            have : p.degree = n := h_sign.1
            have h_deg_nat: p.degree = ↑p.natDegree := Polynomial.degree_eq_natDegree h_p_nonzero
            rw [h_deg_nat] at this
            exact_mod_cast this
          have : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * r^i = ∑ i ∈ Finset.range (n + 1), p.coeff i * r^i := by
            rw [h_deg]
          rw [← h_eval_def, h_root] at this
          exact this.symm
        have h_split : ∑ i ∈ Finset.range (n + 1), p.coeff i * r^i = p.coeff n * r^n + ∑ i ∈ Finset.range n, p.coeff i * r^i := by
          rw [Finset.sum_range_succ]
          ring
        rw [h_split] at h_eval
        have : ∑ i ∈ Finset.range n, p.coeff i * r^i = -(p.coeff n * r^n) := by linarith [h_eval]
        rw [this]
        simp [abs_neg]
      have h_lhs : |p.coeff n * r^n| = |r|^n := by
        have : p.coeff n = 1 ∨ p.coeff n = -1 := h_coeff n (le_refl n)
        cases this <;> simp [abs_mul, *]
      have h_rhs : |∑ i ∈ Finset.range n, p.coeff i * r^i| ≤ ∑ i ∈ Finset.range n, |p.coeff i * r^i| := by
        apply abs_sum_le_sum_abs
      have h_bound : ∑ i ∈ Finset.range n, |p.coeff i * r^i| ≤ ∑ i ∈ Finset.range n, |r|^i := by
        apply Finset.sum_le_sum
        intro i hi
        have : p.coeff i = 1 ∨ p.coeff i = -1 := h_coeff i (Finset.mem_range_le hi)
        cases this <;> simp [abs_mul, *]
      have h_geom : ∑ i ∈ Finset.range n, |r|^i = (|r|^n - 1) / (|r| - 1) := by
        have : |r| > 1 := by linarith [h_r]
        have h_ne : |r| ≠ 1 := by linarith
        apply geom_sum_eq
        exact h_ne
      nlinarith
    -- Derive $|r|^(n+1) - 2|r|^n + 1 ≤ 0$.
    have h_ineq : |r|^(n + 1) - 2 * |r|^n + 1 ≤ 0 := by
      have : 0 < (|r| - 1) := by linarith [h_r]
      have : |r|^n * (|r| - 1) ≤ |r|^n - 1 := (le_div_iff₀ this).mp h_triangle_inequality
      ring_nf
      nlinarith
    -- Conclude $1 ≤ |r|^n * (2 - |r|)$.
    have h_final : 1 ≤ |r|^n * (2 - |r|) := by
      have : |r| > 1 := by linarith [h_r]
      have : |r|^(n + 1) = |r|^n * |r| := by rw [pow_succ]
      rw [this] at h_ineq
      have : |r|^n * (2 - |r|) = 2 * |r|^n - |r|^(n + 1) := by ring
      rw [this]
      linarith
    -- Since $n ≤ 3$ and $|r| ≥ 15/8$, prove $|r|^n * (2 - |r|) < 1$, leading to a contradiction.
    have h_bound : |r|^n * (2 - |r|) < 1 := by
      have h_r_ge_158 : |r| ≥ 15/8 := le_of_lt h_r
      -- Derive $|r| ≤ 2$ from h_final.
      have h_r_le_2 : |r| ≤ 2 := by
        have h₁: 1 ≤ (2 - |r|) * |r|^n := by rw [mul_comm] at h_final;exact h_final
        have h₂: 0 < |r| := by linarith [h_r]
        have h₃ : (0 : ℝ) < |r|^n := pow_pos h₂ n
        have h₄: 2 - |r| > 0 := by nlinarith
        have h₅: 1 / |r|^n ≤ 2 - |r| := (div_le_iff₀ h₃).mpr h₁
        linarith
      -- Prove $|r|^n * (2 - |r|) ≤ |r|^3 * (2 - |r|)$.
      have : |r|^n * (2 - |r|) ≤ |r|^3 * (2 - |r|) := by
        apply mul_le_mul_of_nonneg_right
        · apply pow_le_pow_right₀
          · linarith
          · exact h_n
        · linarith [h_r_le_2]
      -- Compute upper bound.
      have h_calc : |r|^3 * (2 - |r|) ≤ (15/8)^3 * (2 - 15/8) := by
        have : 2 - |r| ≥ 0 := by linarith [h_r_le_2]
        have : 2 - |r| ≤ 2 - 15/8 := by linarith [h_r_ge_158]
        have : |r| ≥ 3/2 := by linarith [h_r_ge_158]
        have : (15/8)^3 * (2 - 15/8) ≥ |r|^3 * (2 - |r|) := by
          apply monotone_decreasing
          · norm_num
          · exact h_r_ge_158
        linarith
      have h_eval : (15/8)^3 * (2 - 15/8) < 1 := by linarith
      nlinarith
    linarith [h_final, h_bound]
