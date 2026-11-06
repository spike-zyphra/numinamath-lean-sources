import Mathlib

open Real

/- 2.1. Let $f(x)=\frac{1}{1+x}$ where $x$ is a positive real number, and for any positive integer $n$, let

$$

g_{n}(x)=x+f(x)+f(f(x))+\cdots+f(f(\ldots f(x))),

$$

the last term being $f$ composed with itself $n$ times. Prove that
(i) $g_{n}(x)>g_{n}(y)$ if $x>y>0$.
(ii) $g_{n}(1)=\frac{F_{1}}{F_{2}}+\frac{F_{2}}{F_{3}}+\cdots+\frac{F_{n+1}}{F_{n+2}}$, where $F_{1}=F_{2}=1$ and $F_{n+2}=F_{n+1}+F_{n}$ for $n \geq 1$. -/
theorem algebra_228096 {f : ℝ → ℝ} (hf : ∀ x, 0 < x → f x = 1 / (1 + x))
    (g : ℕ → ℝ → ℝ) (hg : ∀ n x, 0 < x → g n x = ∑ i ∈ Finset.range (n + 1), f^[i] x)
    (F : ℕ → ℝ) (hF : ∀ n, 0 < n → F (n + 2) = F (n + 1) + F n)
    (hF1 : F 1 = 1) (hF2 : F 2 = 1) :
    (∀ x y, 0 < x → 0 < y → x > y → g n x > g n y) ∧
    (∀ n, g n 1 = ∑ i ∈ Finset.range (n + 1), F (i + 1) / F (i + 2)) := by
  and_intros
  -- first goal
  . -- first prove f^[2] is strictly monotonous on positives, by simple algebra
    have hf_two_mono : StrictMonoOn (f^[2]) (Set.Ioi 0) := by
      rintro a ha b hb hab
      simp at ha hb ⊢
      rw [hf _ ha, hf _ hb, hf _ (by positivity), hf _ (by positivity)]
      field_simp
      convert_to 1 - 1 / (2 + a) < 1 - 1 / (2 + b)
      . field_simp; ring
      . field_simp; ring
      gcongr
    -- next prove that f^[2] is always positive
    have hf_two_pos (x : ℝ) (hx : 0 < x) : 0 < f^[2] x := by
      simp
      rw [hf _ hx, hf _ (by positivity)]
      positivity
    -- now we'll do strong induction
    induction' n using Nat.strong_induction_on with m hm
    rintro x y hx_pos hy_pos h_x_gt_y
    . match m with
      -- for 0, trivially true
      | 0 =>
        simp [hg, hx_pos, hy_pos, h_x_gt_y]
      -- for 1, plug in expression for g and using algebra prove the inequality using positvity
      | 1 =>
        simp [hg, hx_pos, hy_pos, Finset.range, hf]
        suffices 0 < x - y + (1 + x)⁻¹ - (1 + y)⁻¹ by linarith
        convert_to 0 < (x - y) * (x * y + x + y) / ((1 + x) * (1 + y))
        . field_simp
          ring
        have : 0 < x - y := by linarith
        positivity
      -- for k + 2,
      | k + 2 =>
        -- first write g_k(a) as g_1(a) + g_k(f^[2](a))
        have h_g_add_two (a : ℝ) (ha : 0 < a) : g (k + 2) a = g 1 a + g k (f^[2] a) := by
          rw [hg _ _ ha, hg _ _ ha, hg _ _]
          pick_goal 2
          . simp
            rw [hf _ ha, hf _ (by positivity)]
            positivity
          -- write the sums using Ico manipulation to prove equality
          rw [show ∑ i ∈ Finset.range (1 + 1), f^[i] a = a + f a by simp [Finset.range]; ring]
          simp_rw [← Function.iterate_add_apply]
          rw [Finset.range_eq_Ico, show k + 2 + 1 = k + 1 + 2 by ring]
          rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_eq_sum_Ico_succ_bot (by omega), ← add_assoc]
          simp
          nth_rw 1 [show 2 = 0 + 2 by norm_num]
          rw [← Finset.sum_Ico_add]
          rw [← Finset.range_eq_Ico]
          congr
          simp_rw [add_comm, Function.iterate_add_apply]
          congr
        -- now write the g using last fact, then prove the two terms are increasing
        rw [h_g_add_two _ hx_pos, h_g_add_two _ hy_pos]
        gcongr
        . apply hm _ (by omega) _ _ hx_pos hy_pos h_x_gt_y
        . apply hm k (by omega) _ _ (hf_two_pos x hx_pos) (hf_two_pos y hy_pos)
          apply hf_two_mono
          . simpa
          . simpa
          . assumption
  -- second fact
  . rintro n
    -- first prove F i is always positive using induction
    have h_F_pos (i : ℕ) (h : 0 < i) : 0 < F i := by
      induction' i using Nat.twoStepInduction with m hm hm'
      . norm_num at h
      . rw [hF1]; norm_num
      . match m with
        | 0 => simp [hF2]
        | k + 1 =>
          rw [hF _ (by omega)]
          specialize hm (by omega)
          specialize hm' (by omega)
          linarith
    -- now we can prove f^[i] 1 = F (i + 1) / F (i + 2) by using induction
    have h_f_iter_1 (i : ℕ) : f^[i] 1 = F (i + 1) / F (i + 2) := by
      induction' i with m hm
      . simp [hF1, hF2]
      . nth_rw 1 [add_comm]
        rw [Function.iterate_add_apply, Function.iterate_one, hm]
        have h1 := h_F_pos (m + 1) (by omega)
        have h2 := h_F_pos (m + 2) (by omega)
        have h3 := h_F_pos (m + 3) (by omega)
        have : 0 < F (m + 1) / F (m + 2) := by
          positivity
        rw [hf _ this]
        rw [hF (m + 1) (by omega)]
        ring_nf at h1 h2 h3 ⊢
        field_simp [h2.ne.symm]
        ring
    -- the last fact allows writing the expression to target
    rw [hg n 1 (by norm_num)]
    simp_rw [h_f_iter_1]