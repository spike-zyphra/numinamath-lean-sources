import Mathlib

/- Let $f_1(x) = \frac{2}{3} - \frac{3}{3x + 1}$, and for $n \ge 2$, define $f_n(x) = f_1(f_{n - 1}(x))$. The value of $x$ that satisfies f_{1001}(x) = x - 3$ can be expressed in the form $\frac{m}{n}$, where
$m$ and $n$ are relatively prime positive integers. Find $m + n$. -/
theorem algebra_95256 {f : ℕ → ℝ → ℝ}
    (hf1 : ∀ x, f 1 x = 2 / 3 - 3 / (3 * x + 1))
    (hfn : ∀ n ≥ 2, ∀ x, f n x = f 1 (f (n - 1) x)) :
    ∀ (x : ℝ) (m n : ℕ), 3 * x + 1 ≠ 0 ∧ (∀ k > 0, 3 * f k x + 1 ≠ 0) ∧
      f 1001 x = x - 3 ∧ x = m / n ∧ Nat.Coprime m n → m + n = 8 := by
  rintro x m n ⟨hx0, hxk, hf1001, hx_eq, hmn⟩
  -- from the assumption 3 * f 1 x + 1 ≠ 0 derive that 6 - 9 * x ≠ 0
  have hineq1 : 6 - 9 * x ≠ 0 := by
    specialize hxk 1 zero_lt_one
    contrapose! hxk
    field_simp [hf1]
    linarith
  -- an auxiliary inequality
  have hineq2: -18 + x * 27 ≠ 0 := by
    contrapose! hineq1
    linarith
  -- evaluate f for n = 2, 3, 4
  have hf2 : f 2 x = (3 * x + 7) / (6 - 9 * x) := by
    simp [hfn, hf1]
    field_simp
    ring_nf
    field_simp
    ring
  have hf3 : f 3 x = x := by
    simp [hfn 3, hf2, hf1]
    field_simp
    ring
  -- the key property of f is that f 4 x = f 1 x
  have hf4 : f 4 x = f 1 x := by simp [hfn 4, hf3]
  -- generalize the key property of f: for all k we have f (3 * k + 1) x = f 1 x
  have hf : ∀ k, f (3 * k + 1) x = f 1 x := by
    -- proof by induction
    intro k
    induction k with
    | zero => rw [mul_zero, zero_add]
    | succ n ih =>
      -- the induction step follows from the property of f (hfn) and from the induction hypothesis
      rw [←hf4, mul_add, mul_one, add_assoc]; norm_num
      simp [hfn, ih]
  -- now we can compute the value of f 1001 x by finding that 1001 = 3 * 333 + 2
  have eq1001: f 1001 x = (3 * x + 7) / (6 - 9 * x) := by
    rw [hfn _ (by norm_num), show 1001 - 1 = 3 * 333 + 1 by norm_num, hf]
    rw [← hf2, hfn _ (le_refl 2)]
  -- factorize the equation f 1001 x = x - 3
  have h_factor : f 1001 x - (x - 3) = (3 * x - 5) ^ 2 / (6 - 9 * x) := by
    rw [eq1001]
    field_simp
    ring
  -- from the factorization of the equation hf1001 we show that x = 5 / 3
  have x_eq : x = 5 / 3 := by
    rw [← sub_eq_zero, h_factor, div_eq_zero_iff, sq_eq_zero_iff] at hf1001
    cases hf1001 with
    | inl h => linarith
    | inr h => contradiction
  -- it is left to show that m = 5 and n = 3
  -- we need to consider m / n = 5 / 3 as an equality over integers and rational numbers in order to apply Rat.div_int_inj
  have hrat : (m : ℤ) / (n : ℤ) = ((5 : ℤ) : ℚ) / (3 : ℤ) := by
    rify
    rw [← hx_eq, x_eq]
  -- apply Rat.div_int_inj and finish the proof
  apply Rat.div_int_inj at hrat <;> try simp
  · omega
  · cases n with
    | zero => contrapose hx_eq; rw [x_eq]; norm_num
    | succ n => exact Nat.zero_lt_succ n
  · assumption
  · norm_num