import Mathlib

/- 4. Given a sequence of positive terms $\left\{a_{n}\right\}$ satisfying $a_{n}^{n}+a_{n}-1=0$ $\left(n \in \mathbf{N}^{*}\right)$. Below are 5 statements: (1) $0 < a_{n} \leqslant$ $\frac{n}{n+1}$; (2) $\frac{n}{n+1} \leqslant a_{n}< 1$; (3) $\left\{a_{n}\right\}$ is an increasing sequence; (4) $\left\{a_{n}\right\}$ is a decreasing sequence; (5) $\left\{a_{n}\right\}$ is not a monotonic sequence. The correct statements are
A. (1)(3)
B. (1)(4)
C. (2)(3)
D. (2)(5) -/

-- a lemma that is applying am-gm of n variable on x^n, 1, ..., 1
lemma l_am_gm_on_pow_n (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) : x ≤ (x^n + (n - 1)) / n := by
  let v (i : Fin n) : ℝ := if i = ⟨0, hn⟩ then x^n else 1
  let w (i : Fin n) : ℝ := 1
  have h_w_nonneg (i : Fin n) : 0 ≤ w i := by simp [w]
  have h_w_sum_pos : 0 < ∑ i : Fin n, w i := by simp [w]; exact hn
  have h_v_nonneg (i : Fin n) : 0 ≤ v i := by
    by_cases h : i = ⟨0, hn⟩
    . simp [v, h]
      apply pow_nonneg
      exact hx.le
    . simp [v, h]
  convert Real.geom_mean_le_arith_mean Finset.univ w v (by simp; exact h_w_nonneg)
      h_w_sum_pos (by simp; exact h_v_nonneg) using 1
  . -- the product is simplified to be (x^n)^(n⁻¹)
    simp [w, v]
    rw [Real.pow_rpow_inv_natCast hx.le (by linarith)]
  . -- the sum can be written as two parts, one with just 0th term, one with others
    simp [w]
    rw [← Finset.sum_filter_add_sum_filter_not (p := fun i ↦ i = ⟨0,hn⟩)]
    congr
    . -- first part is x^n simply
      convert_to x ^ n = ∑ i ∈ Finset.filter (fun x => x = ⟨0, hn⟩) (Finset.univ (α := Fin n)), (x ^ n)
      . apply Finset.sum_congr rfl
        rintro i hi
        simp at hi
        simp [v, hi]
      simp
      suffices Finset.filter (fun x => x = ⟨0, hn⟩) (Finset.univ (α := Fin n)) = {⟨0, hn⟩} by simp [this]
      ext i; simp
    . -- second part is sum of 1's, which is n - 1
      convert_to n - 1 = ∑ i ∈ Finset.filter (fun x => x ≠ ⟨0, hn⟩) (Finset.univ (α := Fin n)), (1 : ℝ)
      . apply Finset.sum_congr rfl
        rintro i hi
        simp at hi
        simp [v, hi]
      simp
      suffices Finset.filter (fun x => ¬x = ⟨0, hn⟩) (Finset.univ (α := Fin n)) = {⟨0, hn⟩}ᶜ by
        rw [this, Finset.card_compl]
        simp
        push_cast [hn]
        rfl
      ext i; simp

theorem algebra_287510 {a : ℕ → ℝ} (ha : ∀ n > 0, 0 < a n)
    (h : ∀ n, (a n)^n + a n - 1 = 0) :
    (∀ n > 0, 0 < a n ∧ a n ≤ n / (n + 1)) ∧ StrictMono a := by
  -- first prove the upper bound separately as will be used multiple times
  have h_a_ub (n : ℕ) (hn : n > 0) : a n ≤ n / (n + 1) := by
    specialize h n
    -- use am-gm  from which result is easy to get
    have := l_am_gm_on_pow_n n hn (a n) (ha n hn)
    rw [le_div_iff₀ (by norm_cast)] at this
    rw [le_div_iff₀ (by linarith)]
    linarith
  and_intros
  -- first goal is easy to prove
  . rintro n hn
    simp_rw [ha n hn, h_a_ub n hn]
    trivial
    -- for second goal, a n < 1 by n / n+ 1 bound
  . have h_a_lt_one (n : ℕ) (hn : 0 < n) : a n < 1 := by
      suffices n / (n + 1) < (1 : ℝ) by linarith [h_a_ub n hn]
      rw [div_lt_iff₀ (by linarith)]
      linarith
    -- we will prove consecutive values are increasing
    suffices ∀ n, a n < a (n + 1) by
      exact strictMono_nat_of_lt_succ this
    -- assume if not,then there are two consecutive value nonincreasing
    by_contra h_noninc
    push_neg at h_noninc
    obtain ⟨n, hn⟩ := h_noninc
    have h_eq_n := h n
    have h_eq_n_add_one := h (n + 1)
    -- proving following is enough as that creates contradiction using equation
    suffices a (n + 1) ^ (n + 1) < a n ^ n by linarith
    -- prove the inequality by assumption and < 1
    calc
      _ < a (n + 1) ^ n := by
        ring_nf
        apply mul_lt_of_lt_one_left
        . apply pow_pos
          apply ha
          linarith
        . apply h_a_lt_one
          linarith
      _ ≤ a n ^ n := by
        refine pow_le_pow_left₀ ?_ hn n
        apply LT.lt.le
        apply ha
        linarith