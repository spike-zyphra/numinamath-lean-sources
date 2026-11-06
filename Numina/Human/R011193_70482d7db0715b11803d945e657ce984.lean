import Mathlib

open Complex

/- Let $F(z)=\frac{z+i}{z-i}$ for all complex numbers $z\ne i$, and let $z_n=F(z_{n−1})$ for all positive integers $n$. Given that $z_0=1/137+i$ and $z_{2002}=a+bi$, where $a$ and $b$ are real numbers, find $a+b$. -/
theorem algebra_97790 {F : ℂ → ℂ} (hF : ∀ w, w ≠ I → F w = (w + I) / (w - I))
    (z : ℕ → ℂ) (hz0 : z 0 = 1 / 137 + I) (hzn : ∀ n, z (n + 1) = F (z n)) :
    (z 2002).re + (z 2002).im = 275 := by

    -- Using $w$ instead of $z$ to avoid confusion with the sequence $z$

    -- Useful lemma for the proof when we divide by $1 - i$
    have h_aux₁ : 1 - I ≠ 0 := by intro hn; replace hn := congrArg re hn; simp at hn

    -- We can show that $F(w) = i$ implies $w = 1$ so we need $w\ne 1$ to compute $F(F(w))$. We do this by contradiction
    have hw₀ (w : ℂ) (hwI : w ≠ I) (hw1 : w ≠ 1) : F w ≠ I := by
        intro hFw
        rw [hF w hwI, (div_eq_iff (sub_ne_zero_of_ne hwI)),mul_sub,←sub_left_inj (a:=I)] at hFw
        simp at hFw
        rw [←sub_left_inj (a:=I * w),←one_sub_mul] at hFw
        replace hFw := CancelDenoms.cancel_factors_eq_div hFw h_aux₁
        have h_aux₂ : I * w + 1 - I - I * w = 1 - I := by ring
        rw [h_aux₂,div_self h_aux₁] at hFw
        exact hw1 hFw

    -- Useful lemma when this expression will show up in the calculation of $F(F(w))$
    have h_aux₃ : (I + 1) / (1 - I) = I := by
        rw [div_eq_iff h_aux₁]; ring_nf; simp [Complex.I_sq, add_comm]

    -- We calculate $F(F(w))$ for all $w\ne i, 1$ by clearing the fractions then factorizing and simplifying
    have hF₀ (w : ℂ) (hwI : w ≠ I) (hw1 : w ≠ 1) : F (F w) = (w + 1) / (w - 1) * I := by calc
        F (F w) = (F w + I) / (F w - I) := hF (F w) (hw₀ w hwI hw1)
        _ = ((w + I) / (w - I) + I) / ((w + I) / (w - I) - I) := by rw [hF w hwI]
        _ = ((w + I) + I * (w - I)) / ((w + I) - I * (w - I)) := by field_simp [sub_ne_zero_of_ne hwI]; ring
        _ = (w + I + w * I + 1) / (w + I - w * I - 1) := by simp [mul_sub, mul_comm I w, sub_add_eq_sub_sub,add_assoc]
        _ = ((w + 1) * (I + 1)) / ((w - 1) * (1 - I)) := by ring
        _ = ((w + 1) / (w - 1) )* ((I + 1) / (1 - I)) := by field_simp
        _ = (w + 1) / (w - 1) * I := by rw [h_aux₃]

    -- We show that when $F(F(w)) is defined ($w\ne i, 1$), then $F(F(w))\ne i$. So we can compute $F(F(F(w)))$
    have hw₁ (w : ℂ) (hwI : w ≠ I) (hw1 : w ≠ 1) : F (F w) ≠ I := by
        intro hFw
        rw [hF₀ w hwI hw1] at hFw
        replace hFw : (w + 1) / (w - 1) = 1 := (mul_eq_right₀ (by simp)).1 hFw
        replace hFw := (mul_inv_eq_iff_eq_mul₀ (sub_ne_zero_of_ne hw1)).1 hFw
        simp at hFw
        replace hFw : (1:ℂ) = -1 := by rw [←(add_right_inj w)]; exact hFw
        norm_num at hFw

    -- We calculate $F(F(F(w))) for all $w\ne i, 1$ by clearing the fractions then simplifying
    have hF₁ (w : ℂ) (hwI : w ≠ I) (hw1 : w ≠ 1): F (F (F w)) = w := by calc
        F (F (F w)) = (F (F w) + I) / (F (F w) - I) := hF (F (F w)) (hw₁ w hwI hw1)
        _ = ((w + 1) / (w - 1) * I + I) / ((w + 1) / (w - 1) * I - I) := by rw [hF₀ w hwI hw1]
        _ = ((w + 1) / (w - 1) + 1) / ((w + 1) / (w - 1) - 1) := by rw [←add_one_mul,←sub_one_mul,mul_div_mul_right _ _ (by norm_num)]
        _ = w := by field_simp [sub_ne_zero_of_ne hw1]; ring


    -- We have $z_{n+1} = F(z_{n}) for all $n$, so we need to ensure that $z_{n}$\ne i, 1$ for all $n$ to compute the sequence $(z_{n})$
    -- To do this, we first prove that $F(w)\ne 1$ for all $w\ne i$ (We already know that $F(w)\ne i$ by hw₀ above)
    have hw₂ (w : ℂ) (hwI : w ≠ I) : F w ≠ 1 := by
        intro hFw
        rw [hF w hwI] at hFw
        replace hFw : w + I = w - I := (div_eq_one_iff_eq (sub_ne_zero_of_ne hwI)).1 hFw
        replace hFw : I = -I := by rw [←(add_right_inj w)]; exact hFw
        replace hFw : (1:ℝ) = -1 := congrArg im hFw
        norm_num at hFw

    -- We show that $z_{n}\ne i, 1$ for all n, i.e. that the sequence $(z_{n})$ is well defined, by induction
    have hz₁ (n : ℕ) : z n ≠ 1 ∧ z n ≠ I := by
        induction n with
        | zero =>
            split_ands
            · intro hn; rw [hz0] at hn; replace hn := congrArg re hn; simp at hn
            · intro hn; rw [hz0] at hn; replace hn := congrArg re hn; simp at hn
        | succ n nh =>
            split_ands
            · rw [hzn]; exact hw₂ (z n) nh.2
            · rw [hzn]; exact hw₀ (z n) nh.2 nh.1

    -- We have that $z_{k+3} = F(F(F(z_{k})) = z_{k}$ for all $n$. i.e the sequence $(z_{n})$ is periodic with period 3
    have hz₃ (k : ℕ) : z (k + 3) = z k := by
        rw [hzn, hzn, hzn,hF₁ _ (hz₁ k).2 (hz₁ k).1]

    -- Lemma to show that $z_{2002} = z_{1}$
    have hz₃' (n : ℕ) (k : ℕ) : z (k + 3 * n) = z k := by
        induction n with
        | zero => simp
        | succ n nh => simp [mul_add,←add_assoc,hz₃]; exact nh

    -- We use euclidean division by 3 on 2002 to get 2002 = 1 + 3 * 667
    have h2002 : 2002 = 1 + 3 * 667 := by norm_num

    -- We show that $z_{2002}=z_{1}$ by using the periodicity of the sequence $(z_{n})$
    have hz2002 : z (2002) = z 1 := by rw [h2002]; apply hz₃'

    -- We calculate $z_{1}=F(z_{0})=F(1/137+i)=1+i*274$ so $a=1$ and $b=274$ and $a+b=275$
    rw [hz2002,hzn,hF _ (hz₁ 0).2,hz0]
    ring_nf
    norm_num