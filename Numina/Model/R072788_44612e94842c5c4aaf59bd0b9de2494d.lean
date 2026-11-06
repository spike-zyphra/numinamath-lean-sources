import Mathlib

theorem algebra_162258 (n : ℕ) (h₀ : n = 97236)
    (a b c d e f : ℕ)
    (h₁ : a = n / 9)
    (h₂ : b = 2 * a)
    (h₃ : c = b - 12792)
    (h₄ : d = 3 * c)
    (h₅ : e = c)
    (h₆ : f = n - a - b - c - d - e) :
    a + b + c + d + e + f = n ∧
    a = 10804 ∧ b = 21608 ∧ c = 8816 ∧ d = 26448 ∧ e = 8816 ∧ f = 20744 := by 
  subst h₀
  have ha : a = 10804 := by
    norm_num at h₁ ⊢
    exact h₁
  have hb : b = 21608 := by
    simp [h₂, ha]
  have hc : c = 8816 := by
    simp [h₃, hb]
  have hd : d = 26448 := by
    simp [h₄, hc]
  have he : e = 8816 := by
    simp [h₅, hc]
  have hf : f = 20744 := by
    simp [h₆, ha, hb, hc, hd, he]
    all_goals omega
  have hsum : a + b + c + d + e + f = 97236 := by
    omega
  exact ⟨hsum, ha, hb, hc, hd, he, hf⟩