import Mathlib

/- 22. Given a function $f(x)$ defined on $\mathbf{R}^{+}$ that satisfies the following conditions: (1) For any $x, y$ in the domain, $f(x) + f(y) = f(x y)$; (2) When $x > 1$, $f(x) > 0$. Try to find:
(1) Prove that $f\left(\frac{1}{x}\right) = -f(x)$;
(2) Prove that $f(x)$ is an increasing function on $\mathbf{R}^{+}$;
(3) If $f(3) = 1$, and $a$ is a positive real number, solve the inequality $f(x) - f\left(\frac{1}{2 a - x}\right) \geqslant 2$ for $x$. -/
theorem algebra_125875 {f : ℝ → ℝ} (hf : ∀ x y, 0 < x → 0 < y → f x + f y = f (x * y))
    (hpos : ∀ x > 1, f x > 0) :
    (∀ x, 0 < x → f (1 / x) = -f x) ∧
    StrictMonoOn f (Set.Ioi 0) ∧
    (f 3 = 1 → ∀ a > 0, ∀ x, 0 < x → 2 * a - x > 0 → (f x - f (1 / (2 * a - x)) ≥ 2 ↔
      a ≥ 3 ∧ x ∈ Set.Icc (a - √(a^2 - 9)) (a + √(a^2 - 9)))) := by
  -- Show that f(1 / x) = -f(x) for all x > 0.
  have hinv {x} (hx : 0 < x) : f (1 / x) = -f x := calc
    -- We have f(1 / x) = f(1 / x * x) - f(x) = f(1) - f(x).
    -- It is left to show that f(1) = 0.
    -- f(1) = f(1 * 1) = f(1) + f(1), so f(1) = 0.
    f (1 / x) = f (1 / x * x) - f x := by rw [← hf _ _ (by positivity) hx, add_sub_cancel_right]
    _ = f 1 - f x := by field_simp
    _ = -f x := by linarith [mul_one (1 : ℝ) ▸ hf 1 1 zero_lt_one zero_lt_one]
  -- Show that f is strictly increasing on (0, ∞).
  have hmono : StrictMonoOn f (Set.Ioi 0) := by
    simp only [StrictMonoOn, Set.mem_Ioi]
    intro x hx y hy hxy
    -- Assume that 0 < x < y and show that f(y) - f(x) > 0.
    rw [← sub_pos, ← gt_iff_lt]
    calc
      -- f(y) - f(x) = f(y) + f(1 / x) = f(y / x).
      f y - f x = f y + f (1 / x) := by rw [hinv hx, ← sub_eq_add_neg]
      _ = f (y / x) := by rw [hf _ _ hy (by positivity), mul_one_div]
      -- f(y / x) > 0 because y / x > 1.
      _ > 0 := by
        apply hpos
        rwa [gt_iff_lt, one_lt_div hx]
  refine ⟨fun x => hinv, hmono, ?_⟩
  intro h3 a ha x hx hax
  -- Solve the inequality f(x) - f(1 / (2a - x)) ≥ 2.
  calc
    -- f(x) - f(1 / (2a - x)) = f(x) + f(2a - x) = f(x * (2a - x)) (from the properties of f).
    f x - f (1 / (2 * a - x)) ≥ 2 ↔ f x + f (2 * a - x) ≥ 2 := by
        rw [hinv hax, sub_neg_eq_add]
    -- 2 = 1 + 1 = f(3) + f(3) = f(9).
    _ ↔ f (x * (2 * a - x)) ≥ f (3 * 3) := by
        rw [hf _ _ hx hax]
        rw [← hf 3 3 zero_lt_three zero_lt_three, h3]
        norm_num
    -- f is strictly increasing so f(x(2a - x)) ≥ f(9) is equivalent to
    -- x(2a - x) ≥ 9.
    _ ↔ x * (2 * a - x) ≥ 3 * 3 := by
        rw [ge_iff_le, hmono.le_iff_le (by simp) (by simp; positivity)]
    -- We get x^2 - 2ax + 9 ≤ 0.
    _ ↔ x * x - 2 * a * x + 9 ≤ 0 := by
        rw [ge_iff_le, ← sub_nonpos]
        ring_nf
    -- Show that a ≥ 3.
    _ ↔ a ≥ 3 ∧ x * x - 2 * a * x + 9 ≤ 0 := by
        by_cases ha3 : a ≥ 3
        · simp [ha3]
        -- Assume that a < 3 and show that x^2 - 2ax + 9 > 0 for all x.
        simp [ha3]
        push_neg at ha3
        rw [← gt_iff_lt]
        calc
          -- We have x^2 - 2ax + 9 = (x - a)^2 + (9 - a^2) ≥ 9 - a^2 > 0 for a < 3.
          x * x - 2 * a * x + 9 = (x - a)^2 + (9 - a^2) := by ring
          _ ≥ 0 + (9 - a^2) := by
              gcongr
              apply sq_nonneg
          _ > 0 := by
              simp only [zero_add, gt_iff_lt, sub_pos, show (9 : ℝ) = 3^2 by norm_num]
              apply pow_lt_pow_left₀ ha3 (le_of_lt ha) (by norm_num)
    -- x^2 - 2ax + 9 = (x - (a - √(a^2 - 9)))(x - (a + √(a^2 - 9))).
    _ ↔ a ≥ 3 ∧ (x - (a - √(a^2 - 9))) * (x - (a + √(a^2 - 9))) ≤ 0 := by
        simp only [ge_iff_le, and_congr_right_iff]
        intro h
        suffices (x - (a - √(a^2 - 9))) * (x - (a + √(a^2 - 9))) = x * x - 2 * a * x + 9 by
          rw [this]
        calc
          _ = x * x - 2 * a * x + (a - √(a^2 - 9)) * (a + √(a^2 - 9)) := by ring
          _ = x * x - 2 * a * x + (a^2 - √(a^2 - 9)^2) := by ring
          _ = x * x - 2 * a * x + 9 := by
              rw [Real.sq_sqrt]; ring
              rw [show (9 : ℝ) = 3^2 by norm_num, sub_nonneg]
              apply pow_le_pow_left₀ (by norm_num) h
    -- (x - (a - √(a^2 - 9)))(x - (a + √(a^2 - 9))) iff x ∈ [a - √(a^2 - 9), a + √(a^2 - 9)].
    _ ↔ a ≥ 3 ∧ x ∈ Set.Icc (a - √(a^2 - 9)) (a + √(a^2 - 9)) := by
        simp only [ge_iff_le, Set.mem_Icc, and_congr_right_iff]
        intro ha3
        -- Let c = a - √(a^2 - 9) and d = a + √(a^2 - 9).
        -- (x - c)(x - d) ≤ 0 iff 0 ≤ x - c ∧ x - d ≤ 0 or x - c ≤ 0 ∧ 0 ≤ x - d.
        rw [mul_nonpos_iff]
        simp_rw [sub_nonneg, sub_nonpos]
        constructor
        · intro h
          cases' h with h h
          -- If c ≤ x ≤ d then x ∈ [c, d] = [a - √(a^2 - 9), a + √(a^2 - 9)].
          · exact h
          -- Suppose that x ≤ c and d ≤ x.
          by_cases h3 : a = 3
          -- If a = 3 then we get x ∈ [3, 3].
          · subst a
            norm_num at h ⊢
            exact ⟨h.2, h.1⟩
          -- If 3 < a then x ≤ c ∧ d ≤ x is impossible because c < d.
          contrapose! h
          suffices 0 < √(a^2  - 9) by
            intro h1; linarith
          rw [Real.sqrt_pos, sub_pos, show (9 : ℝ) = 3^2 by norm_num]
          apply pow_lt_pow_left₀ _ (by norm_num) (by norm_num)
          rw [lt_iff_le_and_ne]
          exact ⟨ha3, fun h => h3 h.symm⟩
        · intro h
          exact Or.inl h