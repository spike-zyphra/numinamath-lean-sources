import Mathlib

set_option maxHeartbeats 999999999
/-- The graphs $y=3(x-h)^2+j$ and $y=2(x-h)^2+k$ have y-intercepts of $2013$ and $2014$, respectively, and each graph has two positive integer x-intercepts. Find $h$. -/
theorem algebra_95931 (f1 f2 : ℝ → ℝ) (h : ℕ) j k (e1 : ∀ x, f1 x = 3 * (x - h)^2 + j) (e2 : ∀ x, f2 x = 2 * (x - h)^2 + k) (int1 : f1 0 = 2013) (int2 : f2 0 = 2014) (tw1 : ∃ r1 r2 : ℕ, r1 ≠ r2 ∧ 0 < r1 ∧ 0 < r2 ∧ f1 r1 = 0 ∧ f1 r2 = 0) (tw2 : ∃ r1 r2 : ℕ, r1 ≠ r2 ∧ 0 < r1 ∧ 0 < r2 ∧ f2 r1 = 0 ∧ f2 r2 = 0) : h = 36 := by
  obtain ⟨r1, r2, hra, hpr1, hpr2, hint1, hint2⟩ := tw1
  obtain ⟨R1, R2, HRA, HPR1, HPR2, HINT1, HINT2⟩ := tw2
  -- we get $y=3(x-h)^2+2013-3h^2$.
  have klw x : f1 x = 3 * (x - h)^2 + 2013 - 3 * h^2 := by rw [e1] at *; rw [e2] at *; ring_nf at *; linarith
  -- set both equations to $h^2=\frac{2013-j}{3}$ and $h^2=\frac{2014-k}{2}$, respectively.
  have owi : j = 2013 - 3 * h^2 := by rw [e1] at *; rw [e2] at *; ring_nf at *; linarith
  have owo : k = 2014 - 2 * h^2 := by rw [e1] at *; rw [e2] at *; ring_nf at *; linarith
  /- Both f₁ and f₂ are written in vertex form. For a quadratic of the form
  \[
  a·(x - h)² + \text{(constant)},
  \]
  to have **two distinct real roots**, the constant term must be negative (so that the vertex is below the x-axis). -/
  have ttt : h^2 ≥ 1007 := by
    rw [e1] at *; rw [e2] at *; ring_nf at *; rw [pow_two] at HINT1; ring_nf at HINT1
    have := (quadratic_eq_zero_iff_discrim_eq_sq (a := (2 : ℝ)) (b := -(↑h : ℝ) * 4) (c := (↑h : ℝ)^2 * 2 + k) (by norm_num) R1).mp (by linarith)
    have st2 : discrim (2 : ℝ) (-(↑h : ℝ) * 4) ((↑h : ℝ)^2 * 2 + k) ≥ 0 := by clear * - this; nlinarith
    simp only [discrim, neg_mul, even_two, Even.neg_pow, ge_iff_le, sub_nonneg] at st2
    rw [pow_two] at st2; ring_nf at st2
    have int : k ≤ 0 := by linarith
    rify; linarith
  -- find a reason to factorize 671
  have yq : (2 * h - r1) * r1 = (671 : ℤ) := by rw [e1] at *; rw [e2] at *; ring_nf at *; rify; linarith
  have lwek : 2 * h ≥ r1 := by
    have := (Int.mul_nonneg_iff_of_pos_right (a := (2 * ↑h - ↑r1)) (b := r1) (by assumption_mod_cast)).mp (by rw [yq]; norm_num)
    linarith
  have ty : (2 * h - r1) * r1 = 671 := by zify [lwek]; exact yq
  -- time to factorize
  have wle : r1 ∣ 671 := by clear * - ty; exact Dvd.intro_left (2 * h - r1) ty
  have wlf : r1 ∈ Nat.divisors 671 := by clear * - wle; simp only [Nat.mem_divisors, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, and_true]; exact wle
  rw [(by native_decide : Nat.divisors 671 = {1, 11, 61, 671})] at wlf
  simp only [Finset.mem_insert, Finset.mem_singleton] at wlf
  -- let's do it again!
  have yq2 : (2 * h - r2) * r2 = (671 : ℤ) := by rw [e1] at *; rw [e2] at *; ring_nf at *; rify; linarith
  have lwek2 : 2 * h ≥ r2 := by
    have := (Int.mul_nonneg_iff_of_pos_right (a := (2 * ↑h - ↑r2)) (b := r2) (by assumption_mod_cast)).mp (by rw [yq2]; norm_num)
    linarith
  have ty2 : (2 * h - r2) * r2 = 671 := by zify [lwek2]; exact yq2
  -- time to factorize
  have wle2 : r2 ∣ 671 := by clear * - ty2; exact Dvd.intro_left (2 * h - r2) ty2
  have wlf2 : r2 ∈ Nat.divisors 671 := by clear * - wle2; simp only [Nat.mem_divisors, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, and_true]; exact wle2
  rw [(by native_decide : Nat.divisors 671 = {1, 11, 61, 671})] at wlf2
  simp only [Finset.mem_insert, Finset.mem_singleton] at wlf2
  -- that was an enjoyable ride!
  -- finally let's try all 16 cases
  (obtain wlf2 | wlf2 | wlf2 | wlf2 := wlf2) <;> (obtain wlf | wlf | wlf | wlf := wlf) <;> subst r1 r2 <;> (rw [e1] at *; rw [e2] at *; norm_num at *) <;> try omega
  -- 2 leftover cases
  all_goals {
    ring_nf at *; simp only [pow_two, mul_sub, sub_mul] at *; norm_num at *
    have lw : h = 336 := by linarith
    subst h; norm_num at *; subst j k
    norm_num at *
    ring_nf at *
    have law : (↑R2 - 336 : ℤ)^2 = 111889 := by rw [pow_two, mul_sub, sub_mul]; ring_nf; rify; linarith
    have l2 : ¬IsSquare (111889 : ℤ) := by native_decide
    rw [←law] at l2
    have l3 : IsSquare ((↑R2 - 336 : ℤ)^2) := by apply IsSquare.sq
    exact l2 l3
  }