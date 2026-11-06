import Mathlib

/- Initially Alex, Betty, and Charlie had a total of 444 peanuts. Charlie had the most peanuts, and Alex had the least. The three numbers of peanuts that each person had formed a geometric progression. Alex eats 5 of his peanuts, Betty eats 9 of her peanuts, and Charlie eats 25 of his peanuts. Now the three numbers of peanuts each person has forms an arithmetic progression. Find the number of peanuts Alex had initially. -/
theorem algebra_96773 (a b c : ℕ) (h₀ : a + b + c = 444) (h₁ : c > b) (h₂ : b > a)
(h₃ : ∃ r : ℚ, b = a * r ∧ c = b * r) (hi : 9 ≤ b) (hj : 5 ≤ a) (hk : 25 ≤ c) (h₄ : ∃ d, b - 9 = a - 5 + d ∧ c - 25 = b - 9 + d) :
a = 108 := by
  obtain ⟨r, ⟨h₃, h₆⟩⟩ := h₃
  obtain ⟨d, ⟨h₄, h₅⟩⟩ := h₄
  zify [hi, hj, hk] at h₄ h₅
  zify at *
  -- subtracting the 2 equations, $ar^{2}+-2ar+a=12$, so we have $3ar=432,$ or $ar=144$, which is how much Betty had.
  have ww : a * r = 144 := by
    qify at *
    linarith
  rw [ww] at h₃
  norm_cast at h₃
  subst b
  zify at *
  -- have ll : a < 200 := by zify; omega
  -- have gg : a < 180 := by zify; omega
  have gg : a < 160 := by zify; omega
  have tt : 5 ≤ a := by zify; omega
  -- Now we have $144+\dfrac{144}{r}+144r=444$,
  qify at h₀
  rw [h₆] at h₀
  have nz : r ≠ 0 := by aesop
  have re : (↑a : ℚ) = 144 / r := eq_div_of_mul_eq nz ww
  rw [re] at h₀
  -- or $r+\dfrac{1}{r}=\dfrac{25}{12}$
  have yy : r + 1/r = 25/12 := by
    have yw : 144 / r = 144 * (1 / r) := div_eq_mul_one_div 144 r
    linarith
  -- add and multiply to get a quadratic equation
  have rr : (r * r) / r = r := by simp only [mul_self_div_self]
  conv at yy =>
    left
    left
    rw [←rr]
  rw [←add_div] at yy
  have da : ((r * r + 1) / r) * r = (25 / 12) * r := by rw [yy]
  simp only [div_mul_cancel₀ _ nz] at da
  -- solve quadratic equation
  have lw : (r - 4/3) * (r - 3/4) = 0 := by rw [mul_sub, sub_mul]; linarith
  rw [mul_eq_zero] at lw
  obtain lw | lw := lw
  -- if r = 4 / 3
  · have tt : r = 4 / 3 := by linarith
    subst r
    norm_num at re
    qify
    -- a = 108 as expected
    exact re
  -- if r = 3 / 4
  · have ee : r = 3 / 4 := by linarith
    subst r
    norm_num at h₆
    qify at h₁
    rw [h₆] at h₁
    -- there is contradiction
    norm_num at h₁