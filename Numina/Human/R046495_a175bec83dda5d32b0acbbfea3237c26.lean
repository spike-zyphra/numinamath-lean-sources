import Mathlib

/-
4. The sum of three natural numbers is 3053. If we divide the first number by half of the second, we get a quotient of 3 and a remainder of 5, and if we divide the third number by a quarter of the second, we get a quotient of 5 and a remainder of 3. Find the numbers.
-/
theorem algebra_105251 {a b c : ℕ} (h₀ : a + b + c = 3053)
    (h₁ : a / (b / 2) = 3 ∧ a % (b / 2) = 5) (h₂ : c / (b / 4) = 5 ∧ c % (b / 4) = 3) :
    a = 1223 ∧ b = 812 ∧ c = 1018 := by
        have h3 : b ≠ 0 := by
            by_contra hb
            rw [hb] at h₁
            norm_num at h₁
        have h4 : b / 2 ≠ 0 := by
            by_contra h
            norm_num [h] at h₁
        have h6 : b / 4 ≠ 0 := by
            by_contra h
            norm_num [h] at h₂
        have h7  : a = (b / 2) * 3 + 5 := by
            rw [←Nat.div_add_mod a (b / 2)]
            rw [h₁.left, h₁.right]
        have h8 : c = (b / 4) * 5 + 3 := by
            rw [←Nat.div_add_mod c (b / 4)]
            rw [h₂.left, h₂.right]
        have h9 : a + b + c = 3053 := h₀
        rw [h7, h8] at h9
        have hb : b = 812 := by
            omega
        have ha : a = 1223 := by
            rw [hb] at h7
            norm_num at h7
            omega
        have hc : c = 1018 := by
            rw [hb] at h9
            norm_num at h9
            omega
        exact ⟨ha, hb, hc⟩
