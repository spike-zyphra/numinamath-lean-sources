import Mathlib

open Real

namespace algebra_188548

/- Characterizes the values of `x` for which `cos x = sin x`. -/
lemma cos_eq_sin_iff {x : ℝ} : cos x = sin x ↔ ∃ k : ℤ, x = 1 / 4 * π + k * π := by
  rw [← cos_pi_div_two_sub]
  rw [cos_eq_cos_iff]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    rcases hk with hk | hk
    · use - k
      rw [sub_eq_iff_eq_add, add_assoc, ← two_mul x, add_comm] at hk
      rw [← sub_eq_iff_eq_add] at hk
      field_simp at hk
      ring_nf at hk
      field_simp
      rw [← hk]
      ring_nf
    · rw [sub_eq_iff_eq_add] at hk
      field_simp at hk
      replace hk : k = (1 : ℝ) / 4 := by
        rw [← div_left_inj' (show π ≠ 0 from pi_ne_zero)] at hk
        ring_nf at hk
        field_simp at hk
        field_simp
        exact hk.symm
      field_simp at hk
      norm_cast at hk
      have : (4 : ℤ) ∣ 1 := by
        rw [← hk]
        simp
      absurd this
      norm_num
  · rintro ⟨k, hk⟩
    use - k
    left
    rw [hk]
    field_simp
    ring

end algebra_188548

open algebra_188548

/- 8.009. $\operatorname{ctg} t-\sin t=2 \sin ^{2} \frac{t}{2}$. -/
theorem algebra_188548 {t : ℝ} (ht : sin t ≠ 0) :
    cot t - sin t = 2 * (sin (t / 2)) ^ 2 ↔
    ∃ k : ℤ , t = π / 2 * (4 * k - 1) ∨ t = π / 4 * (4 * k + 1) := by
  -- Since$\sin t \neq 0$.
  /-$$ \begin{aligned} &\frac{\cos t}{\sin t}-\sin t=1-\cos t \\ 
  \iff & \cos t-\sin ^{2} t=\sin t-\sin t \cos t \\ 
  \iff & (\cos t+\sin t \cos t)-\left(\sin ^{2} t+\sin t\right)=0 \\ 
  \iff & \cos t(1+\sin t)-\sin t(1+\sin t)=0 \\ 
  \iff & (1+\sin t)(\cos t-\sin t)=0 \end{aligned} $$-/
  rw [sin_sq_eq_half_sub, cot_eq_cos_div_sin]
  have : cos t / sin t - sin t = 2 * (1 / 2 - cos (2 * (t / 2)) / 2) ↔ (1 + sin t) * (cos t - sin t) = 0 := by
    ring_nf
    field_simp [ht]
    rw [← sub_eq_zero]
    ring_nf
  -- That is to say : 1) $1+\sin t=0$ or 2 ) $\cos t-\sin t=0$.
  rw [this]
  rw [mul_eq_zero, sub_eq_zero]
  nth_rw 1 [add_comm, add_eq_zero_iff_eq_neg]
  constructor
  · intro h
    rcases h with h | h
    -- 1. $\sin t=-1, t_{1}=-\frac{\pi}{2}+2 \pi k=\frac{\pi}{2}(4 k-1), \quad k \in \Z$
    · rw [sin_eq_neg_one_iff] at h
      obtain ⟨k, hk⟩ := h
      use k
      left
      rw [← hk]
      ring
    -- 2. $\cos t=\sin t, t_{2}=\frac{\pi}{4}+\pi n=\frac{\pi}{4}(4 n+1), \quad n \in \Z$
    · rw [cos_eq_sin_iff] at h
      obtain ⟨k, hk⟩ := h
      use k
      right
      rw [hk]
      ring
  -- Easy to verify $t_1, t_2$ satisfies the condition
  · rintro ⟨k, hk | hk⟩
    · left
      rw [sin_eq_neg_one_iff]
      use k
      rw [hk]
      ring
    · right
      rw [cos_eq_sin_iff]
      use k
      rw [hk]
      ring
