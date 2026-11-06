import Mathlib

/- Given that $a$ is the largest negative integer, $b$ is the smallest positive integer, and $c$ is the number with the smallest absolute value, then $a+c-b=$____. -/
theorem algebra_9022 {a b c : ℤ} (ha : IsGreatest {n : ℤ | n < 0} a) (hb : IsLeast {n : ℤ | 0 < n} b) (hc : ∀ n : ℤ, |c| ≤ |n|) : a + c - b = -2 := by
  -- Prove a = -1
  replace ha : a = -1 := by
    obtain ⟨h, k⟩ := ha
    simp [upperBounds] at h k
    -- a is an upper bound of the set of negative integers, so a ≥ -1
    specialize k (by norm_num : -1 < 0)
    -- -1 ≤ a < 0, so a = -1
    omega
  replace hb : b = 1 := by
    obtain ⟨h, k⟩ := hb
    simp [lowerBounds] at h k
    -- b is a lower bound of the set of positive integers, so b ≤ 1
    specialize k (by norm_num : (0 : ℤ) < 1)
    -- 0 < b ≤ 1, so b = 1
    omega
  replace hc : c = 0 := by
    -- c is the number with the smallest absolute value, and thus |c| ≤ |0|
    specialize hc 0
    simp at hc
    exact hc
  rw [ha, hb, hc]
  norm_num
