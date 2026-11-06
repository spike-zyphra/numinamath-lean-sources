import Mathlib

namespace number_theory_267636

-- Use Heron's formula to assert that the area of the triangle formed by a, b, c is equal to n.
def IsTriangle (n : ℕ) := ∃ a b c, a + b + c = n ∧ a ≤ b ∧ b ≤ c ∧ c < a + b ∧ n * (n - 2 * a) * (n - 2 * b) * (n - 2 * c) = 16 * n ^ 2

end number_theory_267636

open Finset
open number_theory_267636

/- 495. Count the Matches. A friend writes that he bought a small box of short matches, each an inch long. He found that he could arrange them in the form of a triangle, the area of which contained as many square inches as there were matches. Then he used 6 matches, and it turned out that from the remaining ones, he could form a new triangle, the area of which contained as many square inches as there were matches left. And after using another 6 matches, he managed to do the same again.

How many matches did he have in the box originally? This number is less than 40.

\section*{VARIOUS PUZZLES} -/
theorem number_theory_267636
    (n : ℕ) (h₁ : n < 40)
    (hn1 : IsTriangle n) (hn2 : IsTriangle (n - 6)) (hn3 : IsTriangle (n - 12)) :
    n = 36 := by
  -- Let m = n - 12.
  set m := n - 12
  -- It is enough to prove that m = 24.
  suffices m = 24 by omega
  -- m matches form a triangle with the area m so we can find natural numbers a, b, c such that
  -- a + b + c = m, a ≤ b ≤ c, a + b > c, and
  -- m (m - 2a) (m - 2b) (m - 2c) = 16 m^2.
  have ⟨a, b, c, heq, hab, hbc, hcab, h⟩ := hn3
  -- Clearly, 0 < m (otherwise a + b > c is impossible).
  have hm0 : 0 < m := by omega
  -- Cancel m in the equality for the triangle area:
  -- (m - 2a) (m - 2b) (m - 2c) = 16 m.
  replace h : (m - 2 * a) * (m - 2 * b) * (m - 2 * c) = 16 * m := by
    apply Nat.mul_left_cancel hm0
    linear_combination h
  -- Prove that m is even and assume that m = 2 * k.
  have ⟨k, hk⟩ : 2 ∣ m := by
    -- 2 divides 16 * m so 2 divides (m - 2a) (m - 2b) (m - 2c).
    have h1 : 2 ∣ 16 * m := by use 8 * m; ring
    rw [← h] at h1
    -- 2 is prime so 2 divides either m - 2a, m - 2b, or m - 2c.
    simp_rw [Nat.prime_two.dvd_mul] at h1
    zify [show m ≥ 2 * a ∧ m ≥ 2 * b ∧ m ≥ 2 * c by omega] at h1 ⊢
    -- In all cases we get 2 divides m.
    rcases h1 with (h1 | h1) | h1 <;> have ⟨k, hk⟩ := h1 <;> [use (k + a); use (k + b); use (k + c)] <;> omega
  rw [hk] at h heq ⊢
  -- m = 2k, so we have the following equality:
  -- (k - a)(k - b)(k - c) = 4k.
  replace h : (k - a) * (k - b) * (k - c) = 4 * k := by
    simp_rw [← Nat.mul_sub] at h
    apply Nat.mul_left_cancel (show 0 < 8 by norm_num)
    linear_combination h
  have ineq : k > 0 ∧ k ≥ a ∧ k ≥ b ∧ k ≥ c := by omega
  -- Prove that k ≥ 11.
  have h11 : 11 ≤ k := by
    suffices 10 < k by omega
    -- It is enough to show that k > 10 over real numbers.
    rify [ineq] at heq h ⊢
    rify at ineq
    have hw : (0 : ℝ) ≤ 1 / 3 := by norm_num
    -- Define x = k - a, y = k - b, z = k - c.
    set x : ℝ := k - a
    set y : ℝ := k - b
    set z : ℝ := k - c
    have ⟨hx, hy, hz⟩ : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z := by dsimp [x, y, z]; constructorm* _ ∧ _ <;> linarith
    -- We have x + y + z = 3 * k - (a + b + c) = 3 * k - 2 * k = k.
    have hsum : x + y + z = k := by linear_combination -heq
    -- We also have x y z = 4k.
    -- Apply AM-GM inequality to x, y, z and obtain:
    -- (x y z)^(1/3) ≤ (x + y + z) / 3.
    have ineq := Real.geom_mean_le_arith_mean3_weighted hw hw hw hx hy hz (by norm_num)
    -- We have (4k)^(1/3) ≤ k / 3.
    rw [← Real.mul_rpow hx hy, ← Real.mul_rpow (by positivity) hz, h] at ineq
    simp_rw [← mul_add, hsum] at ineq
    apply Real.rpow_le_rpow (z := 3) (by positivity) at ineq
    simp at ineq
    rw [Real.mul_rpow (by norm_num) (by linarith)] at ineq
    norm_num at ineq
    rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.rpow_add (by linarith), Real.rpow_one] at ineq
    -- Simplify this inequality and get 0 ≤ k * (k^2 - 108).
    replace ineq : 0 ≤ k * (k ^ (2 : ℝ) - (108 : ℝ)) := by linarith
    -- 0 < k so we have 108 ≤ k^2.
    rw [mul_nonneg_iff_right_nonneg_of_pos (by linarith), sub_nonneg, Real.rpow_two] at ineq
    -- We obtain 10 < k.
    rw [← sq_lt_sq₀ (by norm_num) (by linarith)]
    exact lt_of_lt_of_le (by norm_num) ineq
  -- Prove that k cannot be prime.
  have hp : ¬ Nat.Prime k := by
    -- Suppose that k is prime.
    intro hp
    -- If we can show that k divides either a, b, or c, then we get a contradiction
    -- (because k > max(a, b, c)).
    suffices k ∣ a ∨ k ∣ b ∨ k ∣ c by
      rcases this with h | h | h <;> (apply Nat.le_of_dvd (by omega) at h; omega)
    -- k divides 4 k = (k - a) (k - b) (k - c).
    have hk : k ∣ (k - a) * (k - b) * (k - c) := ⟨4, by rw [mul_comm _ 4]; exact h⟩
    -- k is prime so k divides either k - a, k - b, or k - c.
    simp_rw [hp.dvd_mul] at hk
    zify [ineq] at hk ⊢
    -- If (for example) k divides k - b then k divides b.
    -- So we obtain that k either divides a, b, or c.
    rcases hk with (hk | hk) | hk <;> have ⟨x, hx⟩ := hk
    · left; use 1 - x; linarith
    · right; left; use 1 - x; linarith
    · right; right; use 1 - x; linarith
  -- 2 * k = m = n - 12 and n < 40 so k < 14.
  -- We proved that k ≥ 11 so k = 11, k = 12, or k = 13.
  -- k = 11 and k = 13 are impossible because k cannot be prime.
  -- We conclude that k = 12 and n = 2 * k + 12 = 36.
  rcases show k = 11 ∨ k = 12 ∨ k = 13 by omega with hk | hk | hk
  · subst k; norm_num at hp
  · rw [hk]
  · subst k; norm_num at hp