import Mathlib

open Real Set
open scoped Real

theorem algebra_189387 (x : ℝ) : sin (3 * x) - 4 * sin x * cos (2 * x) = 0 ↔
    (∃ n : ℤ, x = n * π) ∨ (∃ k1 : ℤ, x = π / 6 * (6 * k1 + 1)) ∨ (∃ k2 : ℤ, x = π / 6 * (6 * k2 - 1)) := by 
  --rewrite the equation in the simpler form sin x * (4 * sin x ^ 2 - 1) = 0
  have : sin (3 * x) - 4 * sin x * cos (2 * x) = sin x * (4 * sin x ^ 2 - 1) := by 
    --it can be done because 4sinxcos(2x)=2(sin(x-2x)+sin(x+2x)), using the formulas of the sine of the addition, the sine of the subtraction and simple linear arithmetic.
    have eq1 : 4 * sin x * cos (2 * x) = 2 * (sin (x - 2 * x) + sin (x + 2 * x)) := by 
        rw[sin_add, sin_sub]
        ring_nf
    --and moreover sin(3x)=3sinx-4sin³x, using the fact that sin(3x)= sin(x+2x) and the formulas of the sine of addition, sine of twice an angle and linear arithmetic.
    have eq2 : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by 
        rw[(by linarith : 3 * x = x + 2 * x), sin_add, sin_two_mul, cos_two_mul]
        ring_nf
        rw[cos_sq']
        linarith
    --substitute this two equalities in the original equation to find the claim
    rw[eq1]
    ring_nf
    rw[sin_neg, (by linarith : x * 3 = 3 * x)]
    rw[eq2]
    ring_nf
  rw[this]
  constructor
  --now the multiplication is zero if both factors are 0
  · intro h
    rw[mul_eq_zero] at h
    obtain factor1|factor2 := h
    --assume sin x = 0 then one finds that x = kπ
    · rw [(by norm_num : 0 = sin 0), sin_eq_sin_iff] at factor1
      left
      obtain ⟨k,x1|x2⟩ := factor1
      · use - 2 * k
        push_cast
        linarith
      · use 2 * k + 1
        push_cast
        linarith
    --assume 4 * sin²x - 1 = 0, then this is a second order equation in sin(x), and either sin(x)=1/2 or sin(x)=-1/2
    · have root12 : sin x - 1 / 2 = 0 ∨ sin x + (1 / 2) = 0 := by 
        rw[← mul_eq_zero]
        ring_nf
        field_simp
        linarith
      right
      obtain root1|root2 := root12
      --in the first case sin(x)=1/2 one finds that x = π/6 + 2kπ for some k
      · have sin_eq : sin x = sin (π / 6) := by norm_num; linarith
        rw[sin_eq_sin_iff] at sin_eq
        obtain ⟨k,x1|x2⟩ := sin_eq
        · left
          use - 2 * k
          push_cast
          linarith
        · right
          use 2 * k + 1
          push_cast
          linarith
      --in the second case sin(x)=-1/2 one finds that x = -π/6 + 2kπ for some k
      · have sin_eq : sin x = sin (- (π / 6)) := by norm_num; linarith
        rw[sin_eq_sin_iff] at sin_eq
        obtain ⟨k,x1|x2⟩ := sin_eq
        · right
          use - 2 * k
          push_cast
          linarith
        · left
          use 2 * k + 1
          push_cast
          linarith
  --conversely, starting with the given solutions x = nπ and x = ± π/6 + kπ one finds by simple substitution that the equation is fulfilled 
  · intro h
    obtain ⟨n,hn⟩|⟨k1,hk1⟩|⟨k2,hk2⟩ := h
    · rw[hn]
      --to do so we distinguish the cases n even and n odd and we exploit the fact that sin(x+2πn) = sin(x)
      by_cases hyp_n : Even n
      · unfold Even at hyp_n
        obtain ⟨r, hr⟩ := hyp_n
        ring_nf at hr
        rw[hr]
        push_cast
        rw[← zero_add (r * 2 * π), mul_assoc, sin_add_int_mul_two_pi 0 r]
        norm_num
      · have odd_n : Odd n := by exact Int.not_even_iff_odd.1 hyp_n
        unfold Odd at odd_n
        obtain ⟨r, hr⟩ := odd_n
        rw[hr]
        push_cast
        rw[(by linarith : (2 * r + 1) * π = π + r * (2 * π))]
        rw[sin_add_int_mul_two_pi π r]
        norm_num
    --we do the same in the second case, distinguishing k1 even and k1 odd and we exploit the fact that sin(x+2πk₁) = sin(x)
    · rw[hk1]
      by_cases hyp_k1 : Even k1
      · unfold Even at hyp_k1
        obtain ⟨r, hr⟩ := hyp_k1
        ring_nf at hr
        rw[hr]
        push_cast
        ring_nf
        rw[(by linarith : π * (1 / 6) + (π * r * 2) = π / 6 + r * (2 * π))]
        rw[sin_add_int_mul_two_pi (π / 6) r]
        norm_num
      · have odd_k1 : Odd k1 := by exact Int.not_even_iff_odd.1 hyp_k1
        unfold Odd at odd_k1
        obtain ⟨r, hr⟩ := odd_k1
        rw[hr]
        push_cast
        ring_nf
        rw[(by linarith : π * (7 / 6) + (π * r * 2) = (π / 6 + π) + r * (2 * π))]
        rw[sin_add_int_mul_two_pi (π / 6 + π) r]
        norm_num
    --we do the same in the third case, distinguishing k2 even and k2 odd and we exploit the fact that sin(x+2πk₂) = sin(x)
    · rw[hk2]
      by_cases hyp_k2 : Even k2
      · unfold Even at hyp_k2
        obtain ⟨r, hr⟩ := hyp_k2
        ring_nf at hr
        rw[hr]
        push_cast
        ring_nf
        rw[(by linarith : π * (-1 / 6) + (π * r * 2) = -(π / 6) + r * (2 * π))]
        rw[sin_add_int_mul_two_pi (-(π / 6)) r]
        norm_num
      · have odd_k2 : Odd k2 := by exact Int.not_even_iff_odd.1 hyp_k2
        unfold Odd at odd_k2
        obtain ⟨r, hr⟩ := odd_k2
        rw[hr]
        push_cast
        ring_nf
        rw[(by linarith : π * (5 / 6) + (π * r * 2) = (-(π / 6) + π) + r * (2 * π))]
        rw[sin_add_int_mul_two_pi (-(π / 6) + π) r]
        norm_num