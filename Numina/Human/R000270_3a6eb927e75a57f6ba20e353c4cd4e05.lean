import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat
/- The coefficients  $a,b,c$  of a polynomial $f:\mathbb{R}\to\mathbb{R}, f(x)=x^3+ax^2+bx+c$ are mutually distinct integers and different from zero. Furthermore,  $f(a)=a^3$  and $f(b)=b^3.$  Determine  $a,b$  and  $c$ .   -/
theorem number_theory_8770 (a b c : ℤ) (f : ℝ → ℝ) (h₀ : a ≠ 0) (h₁ : b ≠ 0) (h₂ : c ≠ 0) (h₃ : a ≠ b) (h₄ : a ≠ c) (h₅ : b ≠ c) (h₆ : f = (fun (x:ℝ)  => x^3 + a * x^2 + b * x + c)) (h₇ : f a = a^3) (h₈ : f b = b^3) : a = -2 ∧ b = 4 ∧ c = 16 := by
-- subsititute f(a)=a^3 and f(b)=b^3, get heq1 and heq2
have heq1: a^3 + b*a + (c:ℝ) = 0 := by
    have h1: (a^3:ℝ) + a* a^2 + b * a + c = a^3 := by
        have: f a = a^3 + a * a^2 + b*a + c := by simp [h₆]
        rw [← this]
        exact h₇
    have h2: (a*a^2:ℝ) + b*a + c = 0 := by
        rw [add_assoc, add_assoc] at h1
        nth_rewrite 2 [← add_zero (a^3:ℝ)] at h1
        rw [add_assoc]
        apply add_left_cancel h1
    have: (a:ℝ)*a^2 = (a:ℝ)^3 := by ring
    rwa [this] at h2
have heq2: (a+1)*b^2 + (c:ℝ) = 0 := by
    have h1: (b^3:ℝ) + a*b^2 + b*b + c = b^3 := by
        have: f b = b^3 + a*b^2 + b*b + c := by simp [h₆]
        rw [← this]
        exact h₈
    have h2: (a:ℝ)*b^2+b*b+c = 0 := by
        rw [add_assoc,add_assoc] at h1
        nth_rewrite 2 [← add_zero (b^3:ℝ)] at h1
        rw [add_assoc]
        apply add_left_cancel h1
    have: (a:ℝ)*b^2 + b*b = (a+1:ℝ)*b^2 := by ring
    rwa [this] at h2
-- heq1 - heq2
have heq3: (a^3:ℝ)+b*a-(a+1)*b^2 = 0 := by
    have h1: (a^3:ℝ)+b*a = a^3+b*a+c-c := by simp
    rw [h1, heq1]
    have h2: (a+1:ℝ)*b^2 = (a+1)*b^2+c-c := by simp
    rw [h2, heq2]
    simp
-- factor at heq3
have heq4: (a-b:ℝ)*(a*(a+b)+b) = 0 := by
    have h1: (a^3:ℝ)+b*a-(a+1)*b^2 = (a-b:ℝ)*(a*(a+b)+b) := by ring
    rwa [h1] at heq3
have abnz: (a:ℝ) - b ≠ 0 := by
    have h1: (a:ℝ) ≠ b := by simp [h₃]
    simp [h1]
    exact sub_ne_zero_of_ne h1
have heq5: a*(a+b)+(b:ℝ) = 0 := eq_zero_of_ne_zero_of_mul_left_eq_zero abnz heq4
have hb: (b:ℝ) = - (a^2 / (a+1)) := by
    have h1: (a:ℝ)*(a+b)+b = b*(a+1)+(a^2:ℝ) := by ring
    rw [h1] at heq5
    have h2: b*(a+1) = - (a^2:ℝ) := Eq.symm (neg_eq_of_add_eq_zero_left heq5)
    have h3: (a+1:ℝ) ≠ 0 := by
        intro hcon
        have: (a:ℝ) = -1 := Eq.symm (neg_eq_of_add_eq_zero_left hcon)
        rw [hcon, this, mul_zero] at h2
        simp at h2
    field_simp [h2, h3]
-- since b is integer, so a^2/(a+1) must be integer.
have hane: a ≠ -1 := by
    intro hcon
    rw [hcon] at hb
    simp at hb
    rw [hcon, hb] at heq5
    simp at heq5
have ha': (a+1) ∣ a^2 := by
    use (-b)
    have hnz: a+1 ≠ 0 := by
        by_contra hcon
        have: a = -1 := Int.eq_of_sub_eq_zero hcon
        contradiction
    let aa := (a+1) * -b
    have haa: aa = (a+1) * -b := rfl
    let a2 := a^2
    have ha2: a2 = a^2 := rfl
    have h1: (a2:ℝ) = (aa:ℝ) := by
        rw [haa, ha2]
        simp
        rw [hb]
        simp
        rw [mul_comm]
        have hnz': (a:ℝ)+1 ≠ 0 := by
            by_contra hcon
            have h1: (a:ℝ) = -1 := Eq.symm (neg_eq_of_add_eq_zero_left hcon)
            rw [h1] at hb
            simp at hb
            rw [h1, hb] at heq5
            simp at heq5
        exact Eq.symm (div_mul_cancel₀ (a ^ 2 : ℝ) hnz')
    rw [← haa, ← ha2]
    apply Int.cast_inj.mp h1
-- prove that a+1 divides a^2 leads to |a+1| = 1. Then, since a ≠ 0, so a = -2
have advd: (a+1) ∣ 1 := by
    have h1: a^2 = (a+1)*(a-1)+1 := by ring
    rw [h1] at ha'
    have h2: (a+1) ∣ (a+1) * (a-1) := Int.dvd_mul_right (a + 1) (a - 1)
    exact (Int.dvd_iff_dvd_of_dvd_add ha').mp h2
have haeq: a = -2 := by
    rcases advd with ⟨k,hk⟩
    have ht: (a+1) = 1 ∧ k = 1 ∨ (a+1) = -1 ∧ k = -1 := by
        exact Int.eq_one_or_neg_one_of_mul_eq_one' (id (Eq.symm hk))
    rcases ht with ht1 | ht2
    have ht11: a + 1 = 1 := ht1.left
    have h0: a = 0 := by linarith[ht11]
    contradiction
    have ht22: a + 1 = -1 := ht2.left
    linarith [ht22]
-- from a=-2, calculate b and c
have hbeq: b = 4 := by
    have ht: (a:ℝ) = -2 := by simp [haeq]
    rw [haeq] at hb
    norm_num at hb
    apply Int.cast_inj.mp hb
have hceq: c = 16 := by
    have hta: (a:ℝ) = -2 := by simp [haeq]
    have htb: (b:ℝ) = 4 := by simp [hbeq]
    rw [hta, htb] at heq1
    norm_num at heq1
    have htc: (c:ℝ) = 16 := by
        rw [← add_zero 16]
        rw [← heq1]
        simp
    apply Int.cast_inj.mp htc
exact ⟨haeq, hbeq, hceq⟩
