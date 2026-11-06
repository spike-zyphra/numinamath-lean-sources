import Mathlib
set_option maxHeartbeats 500000
/- 4. Given real numbers $a, b, c$ satisfy:

$$

\begin{array}{l}
(a+b)(b+c)(c+a)=a b c, \\
\left(a^{9}+b^{9}\right)\left(b^{9}+c^{9}\right)\left(c^{9}+a^{9}\right)=(a b c)^{9} .
\end{array}

$$


Prove: $a, b, c$ at least one of them is 0. -/
theorem algebra_237462 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h₀ : (a + b) * (b + c) * (c + a) = a * b * c)
    (h₁ : (a ^ 9 + b ^ 9) * (b ^ 9 + c ^ 9) * (c ^ 9 + a ^ 9) = (a * b * c) ^ 9) :
    a = 0 ∨ b = 0 ∨ c = 0 := by

      --We prove the following lemma.
      have lem : ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → x^9 + y^9 ≥ (x + y) * x^4 * y^4 := by
        intro x y hx hy
        --First show x^-xy+y^2 ≥ xy
        have h1 : x^2 - x * y + y^2 ≥ x * y := by
          have : (x - y)^2 ≥ 0 := by positivity
          nlinarith
        --Similarly obtain x^6 - x^3y^3 + y^6 ≥ x^3y^3
        have h2 :  x^6 - x^3 * y^3 + y^6 ≥ x^3 * y^3 := by
          have : (x^3 - y^3)^2 ≥ 0 := by positivity
          nlinarith
        --Now we use h1 and h2.
        calc
          _ = (x + y) * (( x^2 - x * y + y^2) * (x^6 - x^3 * y^3 + y^6)) := by ring
          _ ≥ (x + y) * ((x * y) * (x^3 * y^3)) := by
             --Obviously x * y ≥ 0 or x * y < 0; we need to address both cases here.
            have :  x * y ≥ 0 ∨  x * y < 0 := by exact le_or_lt 0 (x * y)
            --Now we do a case analysis.
            rcases this with h|h
            have cube : x^3 * y^3 ≥ 0 := by
              calc
                _ = (x * y)^3 := by exact Eq.symm (mul_pow x y 3)
                _ ≥ 0^3 := by
                  refine pow_le_pow_left₀ ?_ h 3
                  norm_num
                _ = 0 := by ring_nf
            have : (x * y) * (x^3 * y^3) ≥ 0 := by exact Left.mul_nonneg h cube
            gcongr
            nlinarith

            have cube : x^3 * y^3 < 0 := by nlinarith
            have : (x * y) * (x^3 * y^3) > 0 := by nlinarith
            gcongr
            nlinarith
        nlinarith
        --Done
      --Now we apply lem to a, b , and c, and obtain the following three inequalities.
      have ineq1 : a^9 + b^9 ≥ (a + b) * a^4 * b^4 := by
        apply lem a b
        exact ha; exact hb
      have ineq2 : b^9 + c^9 ≥ (b + c) * b^4 * c^4 := by
        apply lem b c
        exact hb; exact hc
      have ineq3 : c^9 + a^9 ≥ (c + a) * c^4 * a^4 := by
        apply lem c a
        exact hc; exact ha
      --So by multiplying the three inequalities together we obtain the following inequality.
      have ineq4 : (a^9 + b^9) * (b^9 + c^9) * (c^9 + a^9) ≥ ((a + b) * a^4 * b^4) * ((b + c) * b^4 * c^4) * ((c + a) * c^4 * a^4) := by
        gcongr
      --Let's simplify the left hand side and use h₀
      have eq1 : ((a + b) * a^4 * b^4) * ((b + c) * b^4 * c^4) * ((c + a) * c^4 * a^4) = a^9 * b^9 * c^9 := by
        calc
          _ = (a + b) * (b + c) * (c + a) * a^8 * b^8 * c^8 := by ring
          _ = (a * b * c) * a^8 * b^8 * c^8 := by rw [h₀]
          _ = a^9 * b^9 * c^9 := by ring
      --Using ineq4 and eq1 we get the following.
      have ineq5 : (a^9 + b^9) * (b^9 + c^9) * (c^9 + a^9) ≥ a^9 * b^9 * c^9 := by linarith
      --Now by h₁ it follows that (a^9 + b^9) * (b^9 + c^9) * (c^9 + a^9) = a^9 * b^9 * c^9.
      have eq2 : (a^9 + b^9) * (b^9 + c^9) * (c^9 + a^9) = a^9 * b^9 * c^9 := by
        linarith
      --Out goal is to show that at least one of a, b, and c is 0. Let's assume for the sake of a contradiction that none of them is 0.
      --Then a > 0, b > 0, and c > 0.
      --We claim that, in this event, a = b = c. We'll prove this by way of contradiction.
      --Let's first show the strict version of lem.
      have lem_strict : ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → x ≠ y → x^9 + y^9 > (x + y) * x^4 * y^4 := by
        intro x y hx hy hxNEy
        --First show x^-xy+y^2 > xy
        have h1 : x^2 - x * y + y^2 > x * y := by
          have : (x - y)^2 > 0 := by
            refine pow_two_pos_of_ne_zero ?_
            exact sub_ne_zero_of_ne hxNEy
          nlinarith
         --Similarly obtain x^6 - x^3y^3 + y^6 > x^3y^3
        have h2 :  x^6 - x^3 * y^3 + y^6 > x^3 * y^3 := by
          have : (x^3 - y^3)^2 > 0 := by
            refine pow_two_pos_of_ne_zero ?_
            refine sub_ne_zero_of_ne ?_
            simp_all only [ge_iff_le, le_refl, ne_eq, gt_iff_lt, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀]
          nlinarith
        calc
            _ = (x + y) * (( x^2 - x * y + y^2) * (x^6 - x^3 * y^3 + y^6)) := by ring
            _ > (x + y) * ((x * y) * (x^3 * y^3)) := by
              --Obviously x * y ≥ 0 or x * y < 0; we need to address both cases here.
              have :  x * y ≥ 0 ∨  x * y < 0 := by exact le_or_lt 0 (x * y)
              --Now we do a case analysis.
              rcases this with h|h
              have cube : x^3 * y^3 ≥ 0 := by
                calc
                  _ = (x * y)^3 := by exact Eq.symm (mul_pow x y 3)
                  _ ≥ 0^3 := by
                    refine pow_le_pow_left₀ ?_ h 3
                    norm_num
                  _ = 0 := by ring_nf
              have : (x * y) * (x^3 * y^3) ≥ 0 := by exact Left.mul_nonneg h cube
              gcongr
              nlinarith

              have cube : x^3 * y^3 < 0 := by nlinarith
              have : (x * y) * (x^3 * y^3) > 0 := by nlinarith
              gcongr
              nlinarith

                  _ = (x + y) * x^4 * y^4 := by ring

      --Let's assume a ≠ 0 and b ≠ 0 and c ≠ 0 and derive a contradiciton.
      by_contra goal
      have neg_goal : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 := by tauto
      obtain ⟨aNeq0, bNeq0, cNeq0⟩ := neg_goal
      have a_eq_b : a = b := by
        by_contra h
        push_neg at h
        have strict_ineq1 : a^9 + b^9 > (a + b) * a^4 * b^4 := by
          apply lem_strict a b ha hb
          exact h
        --Now we obtain the following strict inequality.
        have strict_ineq2' : (a^9 + b^9) * (b^9 + c^9)  > ((a + b) * a^4 * b^4) * ((b + c) * b^4 * c^4) := by
          have h0 : (a + b) * a^4 * b^4 > 0 := by positivity
          have h1 : b^9 + c^9 > 0 := by positivity
          have h2 : (b + c) * b^4 * c^4 > 0 := by positivity
          have h3 : (a^9 + b^9) * (b^9 + c^9) ≥ (a^9 + b^9) * ((b + c) * b^4 * c^4) := by
            gcongr
          have h4 : (a^9 + b^9) * ((b + c) * b^4 * c^4) > ((a + b) * a^4 * b^4) * ((b + c) * b^4 * c^4) := by
            gcongr
          linarith
        have strict_ineq2 : (a^9 + b^9) * (b^9 + c^9) * (c^9 + a^9)  > ((a + b) * a^4 * b^4) * ((b + c) * b^4 * c^4) * ((c + a) * c^4 * a^4) := by
          have h0 : (a^9 + b^9) * (b^9 + c^9) > 0 := by positivity
          have h1 : (c^9 + a^9) > 0 := by positivity
          have h2 : ((a + b) * a^4 * b^4) * ((b + c) * b^4 * c^4) > 0 := by positivity
          have h3 : ((c + a) * c^4 * a^4) > 0:= by positivity
          have h4 : (a^9 + b^9) * (b^9 + c^9) * (c^9 + a^9) ≥ (a^9 + b^9) * (b^9 + c^9) * ((c + a) * c^4 * a^4) := by
            gcongr
          have h5 : (a^9 + b^9) * (b^9 + c^9) * ((c + a) * c^4 * a^4) > ((a + b) * a^4 * b^4) * ((b + c) * b^4 * c^4) * ((c + a) * c^4 * a^4) := by
            gcongr
          linarith
        --We now obtain a contradiction using eq2 and strict_ineq2.
        simp_all only [ge_iff_le, le_refl, ne_eq, gt_iff_lt, or_self, not_false_eq_true, lt_self_iff_false]
      --Let's now show that b = c. Again by contradiction.
      have b_eq_c : b = c := by
        by_contra h
        push_neg at h
        have strict_ineq1 : b^9 + c^9 > (b + c) * b^4 * c^4 := by
          apply lem_strict b c hb hc
          exact h
        --Now we obtain the following strict inequality.
        have strict_ineq2' : (b^9 + c^9) * (c^9 + a^9)  > ((b + c) * b^4 * c^4) * ((c + a) * c^4 * a^4) := by
          have h0 : (b + c) * b^4 * c^4 > 0 := by positivity
          have h1 : c^9 + a^9 > 0 := by positivity
          have h2 : (c + a) * c^4 * a^4 > 0 := by positivity
          have h3 : (b^9 + c^9) * (c^9 + a^9) ≥ (b^9 + c^9) * ((c + a) * c^4 * a^4) := by
            gcongr
          have h4 : (b^9 + c^9) * ((c + a) * c^4 * a^4) > ((b + c) * b^4 * c^4) * ((c + a) * c^4 * a^4) := by
            gcongr
          linarith
        have strict_ineq2 : (b^9 + c^9) * (c^9 + a^9) * (a^9 + b^9)  > ((b + c) * b^4 * c^4) * ((c + a) * c^4 * a^4) * ((a + b) * a^4 * b^4) := by
          have h0 : (b^9 + c^9) * (c^9 + a^9) > 0 := by positivity
          have h1 : (a^9 + b^9) > 0 := by positivity
          have h2 : ((b + c) * b^4 * c^4) * ((c + a) * c^4 * a^4) > 0 := by positivity
          have h3 : ((a + b) * a^4 * b^4) > 0:= by positivity
          have h4 : (b^9 + c^9) * (c^9 + a^9) * (a^9 + b^9) ≥ (b^9 + c^9) * (c^9 + a^9) * ((a + b) * a^4 * b^4) := by
            gcongr
          have h5 : (b^9 + c^9) * (c^9 + a^9) * ((a + b) * a^4 * b^4) > ((b + c) * b^4 * c^4) * ((c + a) * c^4 * a^4) * ((a + b) * a^4 * b^4) := by
            gcongr
          linarith
        --We now obtain a contradiction using eq2 and strict_ineq2.
        linarith
      --So it follows that a = c as well.
      have c_eq_a : c = a := by linarith
      --Now subsitute a = b , a = c at h₀.
      rw [b_eq_c, c_eq_a] at h₀
      ring_nf at h₀
      --Since a ≠ 0, a^3 ≠ 0.
      have a_cube_neq_0 : a^3 ≠ 0 := by exact pow_ne_zero 3 aNeq0
      --So cancelling out a^3 from h₀ gives 8 = 1, which is a contradiction.
      have contr_8_eq_1 : 7 = 0 := by
        have : 7 * a^3 = 0 := by linarith
        subst a_eq_b b_eq_c
        simp_all only [ge_iff_le, ne_eq, gt_iff_lt, not_false_eq_true, mul_eq_left₀, OfNat.ofNat_ne_one]
      contradiction