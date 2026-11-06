import Mathlib

/- Let $X$ denote the set of all triples $(a, b, c)$ of integers. Define a function $f: X \rightarrow X$ by

$$
f(a, b, c)=(a+b+c, a b+b c+c a, a b c)
$$

Find all triples $(a, b, c)$ in $X$ such that $f(f(a, b, c))=(a, b, c)$. -/
theorem algebra_607823 (f : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ)
    (h₀ : ∀ a b c, f (a, b, c) = (a + b + c, a * b + b * c + c * a, a * b * c)) :
    {(a, b, c) : ℤ × ℤ × ℤ | f (f (a, b, c)) = (a, b, c)} =
    {(t, 0, 0) | t : ℤ} ∪ {(a, b, c) : ℤ × ℤ × ℤ | a = -1 ∧ b = -1 ∧ c = 1} := by 
  ext ⟨a, b, c⟩
  simp
  -- Let us put $a+b+c=d, a b+b c+c a=e$ and $a b c=f$.
  let d := a + b + c
  let e := a * b + b * c + c * a
  let f' := a * b * c
  constructor
  · intro hx
    -- The given condition $f(f(a, b, c))=(a, b, c)$ implies that
    -- v$$ d+e+f=a, \quad d e+e f+f d=b, d e f=c $$
    rw [h₀ a b c, h₀ d e f'] at hx
    simp at hx
    -- Thus $a b c d e f=f c$ 
    have : a * b * c * d * e * f' = f' * c := by nth_rw 2 [← hx.2.2]; ring
    -- and hence either $c f=0$ or $a b d e=1$.
    have : (a * b * d * e - 1) = 0 ∨ c * f' = 0 := by 
      exact eq_zero_or_eq_zero_of_mul_eq_zero (by linarith)
    cases this with
    | inr hcf_eq_0 =>
      -- Case I: Suppose $c f=0$. Then either $c=0$ or $f=0$.
      have hc_or_f_eq_0 := eq_zero_or_eq_zero_of_mul_eq_zero hcf_eq_0
      -- However $c=0$ implies $f=0$ and vice-versa.
      have hc_and_f_eq_0: c = 0 ∧ f' = 0 := by
        cases hc_or_f_eq_0 with
        | inl hc0 =>
          have hf0 : f' = 0 := by unfold f'; rw [hc0]; simp
          exact ⟨hc0, hf0⟩ 
        | inr hf0 =>
          have hc0 : c = 0 := by 
            rw [hf0] at hx; simp at hx; exact Eq.symm hx.2.2
          exact ⟨hc0, hf0⟩ 
      
      have hc0 := hc_and_f_eq_0.1
      have hf0 := hc_and_f_eq_0.2
      have hx1 := hx.1

      -- Thus we obtain $a+b=d, d+e=a, a b=e$ and $d e=b$. 
      nth_rw 1 [show d = a + b + c by rfl] at hx
      rw [hf0, hc0] at hx
      simp at hx

      -- The first two relations give $b=-e$.
      have hb_eq_neg_e: b = - e := by linarith
      nth_rw 2 [hb_eq_neg_e] at hx

      -- Thus $e=a b=-a e$ and $d e=b=-e$.
      have he_eq_ab: e = a * b := by unfold e; rw [hc0]; simp
      have he_eq_neg_ae: a * e = - e := by rw [hb_eq_neg_e] at he_eq_ab; linarith
      -- We get either $e=0$ or $e≠0$.
      cases eq_or_ne e 0 with
      | inl he_eq_0 => 
        -- If $e=0$, then $b=0$ and $a=d=t$,
        have hb0 : b = 0 := by linarith
        -- say. We get the triple $(a, b, c)=(t, 0,0)$, where $t \in \mathbb{Z}$. 
        left; rw [hc0, hb0]; simp
      | inr he_ne_0 =>
        -- If $e \neq 0$, then $a=d=-1$. 
        have ha_neg_1: a = -1 := mul_right_cancel₀ he_ne_0 (by simp [he_eq_neg_ae])
        have hd_neg_1: d = -1 := mul_right_cancel₀ he_ne_0 (by simp [hx.2])
        -- But then $d+e+f=a$ implies that $-1+e+0=-1$ forcing $e=0$. 
        rw [ha_neg_1, hd_neg_1, hf0] at hx1
        simp at hx1
        contradiction

    | inl heq =>
      -- Case II: Suppose $c f \neq 0$. In this case $a b d e=1$. 
      have : a * b * d * e = 1 := by linarith
      cases Int.eq_one_or_neg_one_of_mul_eq_one' this with
      | inl habd_e_eq_1 =>
        cases Int.eq_one_or_neg_one_of_mul_eq_one' habd_e_eq_1.1 with
        | inl hab_d_eq_1 =>
          cases Int.eq_one_or_neg_one_of_mul_eq_one' hab_d_eq_1.1 with
          | inl ha_b_eq_1 =>
            -- Suppose $a=b=d=e=1$. 
            unfold d at hab_d_eq_1
            rw [ha_b_eq_1.1, ha_b_eq_1.2] at hab_d_eq_1
            simp at hab_d_eq_1
            -- Then $a+b+c=d$ shows that $c=-1$. 
            have hc_neg_1: c = -1 := by linarith
            -- Similarly $f=-1$.
            have hf_neg_1: f' = -1 := by 
              unfold f'; rw [hc_neg_1, ha_b_eq_1.1, ha_b_eq_1.2]; simp
            -- Hence $e=a b+b c+c a=1-1-1=-1$ contradicting $e=1$.
            have he_neg_1: e = -1 := by
              unfold e; rw [ha_b_eq_1.1, ha_b_eq_1.2, hc_neg_1]
              simp
            have : e = 1 := by linarith
            have : e ≠ 1 := by linarith
            contradiction
          | inr ha_b_eq_neg_1 =>
            -- Similar to the case of $a=b=1$ and $d=e=-1$, 
            -- the case where $a=b=-1$ and $d=e=1$ is not possible.
            have hc_eq_3 : c = 3 := by 
              unfold d at hab_d_eq_1
              rw [ha_b_eq_neg_1.1, ha_b_eq_neg_1.2] at hab_d_eq_1
              linarith
            have hf_eq_neg_3: f' = -3 := by linarith
            have hf_eq_3: f' = 3 := by 
              unfold f'
              rw [hc_eq_3, ha_b_eq_neg_1.1, ha_b_eq_neg_1.2]
              simp
            have : f' ≠  -3 := by linarith
            contradiction
        | inr hab_d_eq_neg_1 =>
          cases Int.mul_eq_neg_one_iff_eq_one_or_neg_one.mp hab_d_eq_neg_1.1 with
          | inl ha_eq_1_and_b_eq_neg_1 => 
            -- If $a=1, b=-1, d=-1, e=1$, then $c=-1$ and $e=a b+b c+c a=-1+1-1=-1$ and a contradiction to $e=1$. 
            have hc_eq_neg_1 : c = -1 := by 
              unfold d at hab_d_eq_neg_1
              rw [ha_eq_1_and_b_eq_neg_1.1, ha_eq_1_and_b_eq_neg_1.2] at hab_d_eq_neg_1
              linarith
            have he_eq_1: e = 1 := by linarith
            have he_eq_neg_1: e = -1 := by 
              unfold e
              rw [hc_eq_neg_1, ha_eq_1_and_b_eq_neg_1.1, ha_eq_1_and_b_eq_neg_1.2]
              simp
            have : e ≠ -1 := by linarith
            contradiction
          | inr ha_eq_neg_1_and_b_eq_1 => 
            -- Finally if $a=-1, b=1, d=-1$ and $e=1$, then $c=-1$ and $f=-1$. 
            have hc_eq_neg_1 : c = -1 := by 
              unfold d at hab_d_eq_neg_1
              rw [ha_eq_neg_1_and_b_eq_1.1, ha_eq_neg_1_and_b_eq_1.2] at hab_d_eq_neg_1
              linarith
            have hf_eq_1: f' = 1 := by
              unfold f'
              rw [hc_eq_neg_1, ha_eq_neg_1_and_b_eq_1.1, ha_eq_neg_1_and_b_eq_1.2]
              simp
            -- But then $f=a b c$ is not satisfied.
            have : f' = -1 := by linarith
            have : f' ≠ -1 := by linarith
            contradiction
      | inr habd_e_eq_neg_1 =>
        cases Int.mul_eq_neg_one_iff_eq_one_or_neg_one.mp habd_e_eq_neg_1.1 with
        | inl hab_eq_1_and_d_eq_neg_1 => 
          cases Int.eq_one_or_neg_one_of_mul_eq_one' hab_eq_1_and_d_eq_neg_1.1 with
          | inl ha_b_eq_1 => 
            -- Suppose $a=b=1$ and $d=e=-1$. 
            -- Then $a+b+c=d$ gives $c=-3$ and $d+e+f=a$ gives $f=3$.
            have hc_eq_neg_3 : c = -3 := by 
              unfold d at hab_eq_1_and_d_eq_neg_1
              rw [ha_b_eq_1.1, ha_b_eq_1.2] at hab_eq_1_and_d_eq_neg_1
              linarith
            have hf_eq_3: f' = 3 := by linarith
            -- But then $f=a b c=1 \cdot 1 \cdot(-3)=-3$, a contradiction.
            have hf_eq_neg_3: f' = -3 := by 
              unfold f'
              rw [hc_eq_neg_3, ha_b_eq_1.1, ha_b_eq_1.2]
              simp
            have : f' ≠  -3 := by linarith
            contradiction
          | inr hab_eq_neg_1 =>
            -- The only case left is that of $a, b, d, e$ being all equal to -1
            -- Then $c=1$ and $f=1$.
            have hc_eq_1 : c = 1 := by 
              unfold d at hab_eq_1_and_d_eq_neg_1
              rw [hab_eq_neg_1.1, hab_eq_neg_1.2] at hab_eq_1_and_d_eq_neg_1
              linarith
            have hf_eq_1: f' = 1 := by linarith
            -- It is easy to check that $(-1,-1,1)$ is indeed a solution.
            right
            exact ⟨hab_eq_neg_1.1, hab_eq_neg_1.2, hc_eq_1⟩ 
        | inr hab_eq_neg_1_and_d_eq_1 => 
          cases Int.mul_eq_neg_one_iff_eq_one_or_neg_one.mp hab_eq_neg_1_and_d_eq_1.1 with
          | inl ha_eq_1_and_b_eq_neg_1 => 
            -- If $a=1, b=-1, d=1$, $e=-1$, then $a+b+c=d$ gives $c=1$. 
            have hc_eq_1: c = 1 := by 
              unfold d at hab_eq_neg_1_and_d_eq_1
              rw [ha_eq_1_and_b_eq_neg_1.1, 
                  ha_eq_1_and_b_eq_neg_1.2] at hab_eq_neg_1_and_d_eq_1
              linarith
            -- Similarly $f=1$. 
            have hf_eq_1: f' = 1 := by linarith
            -- But then $f=a b c=1 \cdot 1 \cdot(-1)=-1$ a contradiction. 
            have hf_eq_neg_1: f' = -1 := by 
              unfold f'
              rw [hc_eq_1, ha_eq_1_and_b_eq_neg_1.1, ha_eq_1_and_b_eq_neg_1.2]
              simp
            have : f' ≠ -1 := by linarith
            contradiction
          | inr ha_eq_neg_1_and_b_eq_1 => 
            -- Since the case of $a=1, b=-1, d=-1, e=1$ is impossible, The symmetry between $(a, b, c)$ and $(d, e, f)$ shows that $a=-1, b=1, d=1, e=-1$ is not possible. 
            have hc_eq_1: c = 1 := by 
              unfold d at hab_eq_neg_1_and_d_eq_1
              rw [ha_eq_neg_1_and_b_eq_1.1, 
                  ha_eq_neg_1_and_b_eq_1.2] at hab_eq_neg_1_and_d_eq_1
              linarith
            have hf_eq_neg_1: f' = -1 := by 
              unfold f'
              rw [hc_eq_1, ha_eq_neg_1_and_b_eq_1.1, ha_eq_neg_1_and_b_eq_1.2]
              simp
            rw [hf_eq_neg_1, hab_eq_neg_1_and_d_eq_1.2] at hx
            simp at hx
            have hb_eq_neg_1: b = -1 := by linarith
            have : b ≠ -1 := by linarith
            contradiction
      
  · intro hx
    rw [h₀, h₀]
    cases hx with
    | inl hx1 =>
      rcases hx1 with ⟨_, _⟩
      simp
    | inr hx2 =>
      rw [hx2.1, hx2.2.1, hx2.2.2]
      simp
