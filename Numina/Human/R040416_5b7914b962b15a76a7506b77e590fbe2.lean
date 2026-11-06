import Mathlib

open Real

/- Given the sequence $\left\{x_{n}\right\}, x_{1}=1$, and $x_{n+1}=\frac{\sqrt{3} x_{n}+1}{\sqrt{3}-x_{n}}, x_{1999}-x_{601}=$ -/
theorem algebra_131612 (x : ℕ → ℝ) (hx1 : x 1 = 1)
    (hxn : ∀ n, x (n + 1) = (sqrt 3 * x n + 1) / (sqrt 3 - x n)) :
    x 1999 - x 601 = 0 := by
    -- Let $x_{n}=\tan \alpha_{n}$,
    let α (n : ℕ) := arctan (x n)
    have hα : ∀ n , x n = tan (α n) := by
      intro n ;simp [α]
    have h1 : ∀ (l : ℤ), π / 6 ≠ (2 * ↑l + 1) * π / 2 := by
      intro k
      by_contra! 
      apply (div_eq_iff (by simp)).mpr at this
      apply (div_eq_iff (by simp ;exact pi_ne_zero)).mpr at this
      ring_nf at this
      rw [mul_inv_cancel₀ pi_ne_zero,one_mul] at this
      by_cases hk : 1 ≤ k
      · have : (3:ℝ) ≤ 1 + ↑k * 2 := by 
          have : (1:ℤ) ≤ (↑k:ℝ) := by exact Int.cast_le.mpr hk
          simp at this ;nlinarith
        nlinarith
      by_cases hk' : k = 0 
      · simp [hk'] at this
      have : k ≤ -1 := by
        refine Int.not_lt.mp ?_
        contrapose! hk'
        omega
      have : (↑k : ℝ) ≤ ↑(-1 : ℤ) :=  Int.cast_le.mpr this
      simp at this ;nlinarith
    -- then $x_{n+1}=\tan \alpha_{n+1}=\tan \left(\alpha_{n}+\frac{\pi}{6}\right)$, 
    have hxn1 : ∀ n, x (n + 1) = tan (α n + π / 6):= by
      intro n
      rw [tan_add,← hα,hxn]
      norm_num;field_simp;ring
      left;constructor
      · intro k
        simp [α] ;exact arctan_ne_mul_pi_div_two k
      exact h1
    -- so $x_{n+6}=x_{n}$, which means $\left\{x_{n}\right\}$ is a periodic sequence. 
    let β (n : ℕ ) := α 0 + n * π / 6
    have hb : ∀ n, x n = tan (β n) := by
      intro n
      induction' n with n hn
      · simp [β,α]
      · rw[hxn1]
        have : β (n+1) = β n + π / 6:= by simp [β] ;ring
        rw [this,tan_add,tan_add,← hn]
        simp [α]
        left ;constructor
        · intro k
          simp [β]
          by_contra!
          have : ∃ k:ℤ, α 0 = k * π / 6 := by
            have : α 0 = (2 * ↑k + 1) * π / 2 - ↑n * π / 6 := by
              rw [sub_eq_iff_eq_add.mpr this.symm]
            have this' : (2 * ↑k + 1) * π / 2 - ↑n * π / 6 = (6 * ↑k + 3 - ↑n) * π / 6 := by ring
            rw [this,this']
            use (6*k+3-n) ;simp
          obtain ⟨k,hk⟩ := this ;simp [α] at hk
          have h2 := Real.arctan_mem_Ioo (x 0)
          simp [hk] at h2
          have h3 : -(π / 2) * (π / 6)⁻¹ < ↑k  ∧ ↑k  < π / 2 * (π / 6)⁻¹ := by
            rcases h2 with ⟨h21,h22⟩
            constructor
            refine (mul_inv_lt_iff₀ (by simp ;exact pi_pos)).mpr ?_ 
            rw [mul_div] ;exact h21
            refine (lt_mul_inv_iff₀ (by simp ;exact pi_pos)).mpr ?_
            rw [mul_div] ;exact h22
          ring_nf at h3
          rw [mul_inv_cancel₀ (pi_ne_zero),one_mul] at h3
          rcases h3 with ⟨h31,h32⟩
          have h31' : (-3 : ℤ)=(-3:ℝ) := by simp
          rw [← h31'] at h31
          apply Int.cast_lt.mp at h31
          have h32' :(3:ℤ)=(3:ℝ):= by simp
          rw [← h32'] at h32
          apply Int.cast_lt.mp at h32
          specialize hxn1 0
          simp [α] at hxn1
          rw [hk,hx1] at hxn1
          interval_cases k
          <;> ring_nf at hxn1
          · norm_num at hxn1
            rw [mul_div,mul_one] at hxn1
            norm_num at hxn1
            have : (1:ℝ) < 0 := by
              rw [hxn1] ;simp
            linarith
          · simp at hxn1
          · rw [mul_div,mul_one] at hxn1
            norm_num at hxn1
          · rw [mul_div,mul_one] at hxn1
            norm_num at hxn1
            have : 1 = (√3)^2 := by rw [← hxn1] ;simp
            simp at this
          · rw [mul_div,mul_one] at hxn1
            norm_num at hxn1
        exact h1
        left ;constructor
        · intro k
          simp [α] ;exact arctan_ne_mul_pi_div_two k
        exact h1
    have hxn6 : ∀ n, ∀ k , x (n + 6 * k) = x n := by
      intro n k
      rw [hb,hb]
      simp [β]
      induction' k with k hk
      · simp
      rw [← hk]
      have : α 0 + (↑n + 6 * ↑(k + 1)) * π / 6 = α 0 + (↑n + 6 * ↑k) * π / 6 + π := by ring_nf ;rw [Nat.cast_add,add_mul] ;simp ;ring
      rw[this,Real.tan_add_pi (α 0 + (↑n + 6 * ↑k) * π / 6)]
    -- $1999=333 \times 6+1,601=6 \times 100+1$, thus $x_{1999}-x_{601}=0$.
    specialize hxn6 601 233
    rw [← hxn6] ;norm_num


