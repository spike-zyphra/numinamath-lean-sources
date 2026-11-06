import Mathlib

/- 30. The sequence $a_{1}, a_{2}, a_{3}, \ldots$ of real numbers satisfies the recurrence

$$

a_{n+1}=\frac{a_{n}^{2}-a_{n-1}+2 a_{n}}{a_{n-1}+1} .

$$


Given that $a_{1}=1$ and $a_{9}=7$, find $a_{5}$. -/
theorem algebra_188840 {a : ℕ → ℝ} (ha : a 0 = 1) (ha' : a 8 = 7)
    (h : ∀ n, a (n + 2) = (a (n + 1) ^ 2 - a n + 2 * a (n + 1)) / (a n + 1))
    (h_a_pos : ∀ n, a n + 1 ≠ 0) : a 4 = 3 := by
  -- for ease of proving, sequence indices are shifted one left. also equation is written for n, n+1, n+2
  -- we define the sequnce b as b(n) = a(n) + 1, replace everything in terms of b
  set b := fun n => a n + 1 with hb
  have hab (n : ℕ) : a n = b n - 1 := by rw [hb]; simp
  simp_rw [hab] at h
  simp at h
  -- we find that b(n+2) = b(n+1)^2 / b(n)
  have h' (n : ℕ) : b (n + 2) = b (n + 1)^2 / (b n) := by
    have := h_a_pos n
    have := h n
    field_simp at this ⊢
    ring_nf at this ⊢
    linarith
  rw [hab] at ha ha' ⊢
  simp_rw [hab] at h_a_pos; simp at h_a_pos
  clear * - ha ha' h_a_pos h'
  -- this means b is a geometric sequence, prove that using strong induction
  have hb_gen : ∃ r : ℝ, ∀ n, b n = b 0 * r ^ n := by
    have : b 0 ≠ 0 := h_a_pos 0
    have : b 1 ≠ 0 := h_a_pos 1
    set r := b 1 / b 0 with hr
    use r
    intro n
    induction' n using Nat.strong_induction_on with n ih
    match n with
    | 0 => ring
    | 1 => rw [hr]; field_simp
    | n + 2 =>
      have h₁ := ih n (by linarith)
      have h₂ := ih (n+1) (by linarith)
      calc
        b (n + 2) = (b (n + 1) ^ 2) / b n := by rw [← h' n]
        _ = ((b 0 * r^(n+1))^2) / (b 0 * r^n) := by rw [h₁, h₂]
        _ = b 0 * r^(n+2) := by field_simp; ring
  obtain ⟨r, hbr⟩ := hb_gen
  -- now (b(4))^2 = b(0) * b(8), this means b(4)^2 = 4^2.
  -- b(4) = b(0) * r^4, so it's positive, hence b(4) = 4
  have ha : b 0 = 2 := by linarith
  have ha' : b 0 * r ^ 8  = 8 := by rw [← hbr 8]; linarith
  have ha'' : b 4 ^ 2 = 4^2 := by calc
    b 4 ^2 = b 0 * (b 0 * r^8) := by rw [hbr 4]; ring
    _ = 4^2 := by rw [ha', ha]; norm_num
  have : b 4 ≥ 0 := by
    rw [hbr 4, ha]
    positivity
  have : b 4 = 4 := by exact sq_eq_sq₀ this (by norm_num) |>.mp ha''
  rw [this]
  norm_num