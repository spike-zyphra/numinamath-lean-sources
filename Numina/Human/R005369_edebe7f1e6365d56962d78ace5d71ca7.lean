import Mathlib 

/-The positive integer $n$ has the following property: if the three last digits of $n$ are removed, the number $\sqrt[3]{n}$ remains. Find $n$.-/
theorem number_theory_8655 {n : ℕ} (hn : n > 0) (h : (n / 1000 ) ^ 3 = n) :
  n = 32768 := by 
    -- By the condition 'if the three last digits of $n$ are removed, the number $\sqrt[3]{n}$ remains', $1000 < n$. 
    have h1 : 1000 < n := by 
      by_contra! h1
      have : n / 1000 = 0 := by 
        simp [h1]
        have : n ≠ 1000 := fun n1000 => by simp [n1000] at h
        omega
      simp [this] at h
      linarith
    -- let f be the function $f(x) = x^3 - 1000 * x$.
    let f : ℕ → ℝ := fun x => x^3 - 1000 * x 
    -- Then f is an increasing function of x when $31 < x$.
    have hf : StrictMonoOn f (Set.Ioi 31) := by 
      intro a ha b hb hab  
      simp [f] 
      simp at ha hb 
      have l1 : ∀ x, 31 < x → 1000 * x ≤ x^3 := by 
        intro x hx 
        rw [show 3 = 2 + 1 by rfl, pow_add, pow_one]
        exact le_of_lt <| (Nat.mul_lt_mul_right (by omega)).2 (by nlinarith)
      suffices c1 : (0 : ℝ) < (b - a) * (b^2 + a * b + a^2 - 1000) by 
        nlinarith
      apply mul_pos (by simp [hab]) 
      calc 
        _ < 32 * 32 - (1000 : ℝ) := by norm_num
        _ ≤ b * a - (1000 : ℝ) := by 
          apply sub_le_sub (by 
            apply mul_le_mul <;> norm_cast
            linarith ) (by linarith)   
        _ < _ := by apply sub_lt_sub_right; norm_cast; nlinarith
    have hmodn := Nat.div_add_mod n 1000
    nth_rw 3 [←  h] at hmodn 
    have h' : 1000 * (n / 1000) ≤ (n / 1000) ^ 3 := by 
      rw [←hmodn]; simp
    -- Because for any positive number x, $f(x) < 0$ and $0 < f(n/1000)$, 
    -- $31 < n / 1000$.
    have h2 : 31 < n / 1000 := by 
      have : 0 ≤ f (n / 1000) := by simp [f]; norm_cast
      have l2 : ∀ x, 0 < x → x ≤ 31 → f x < 0 := by 
        intro x xpos hx 
        simp [f]
        suffices 0 < x * (1000 - x^2) by 
          norm_cast 
          rw [show x^3 = x^2 * x by rw [show 3 = 2 + 1 by rfl, pow_add, pow_one]]
          apply (Nat.mul_lt_mul_right xpos).2
          nlinarith
        apply mul_pos xpos 
        apply Nat.lt_sub_of_add_lt 
        nlinarith
      by_contra! 
      linarith [l2 (n /1000) (by omega) this]
    -- Because $f(n/1000) < 1000 and 1000 < f(33)$, we get $n/1000 < 33$.
    have h3 : n / 1000 < 33 := by 
      have : (n / 1000) ^ 3 - 1000 * (n / 1000) < 1000 := by 
        suffices (n / 1000) ^ 3 - 1000 * (n / 1000) = n % 1000 by 
          simp [this,  Nat.mod_lt] 
        norm_num [←hmodn]
      have h4 : 1000 < f 33 := by simp [f]; nlinarith
      have : f ((n / 1000 )) < 1000 := by 
        simp [f, this]; norm_cast
      exact (StrictMonoOn.lt_iff_lt hf (by simp [h2]) (by simp)).1 (show f (n / 1000) < f 33 by linarith)
    -- Because $31 < n / 1000 < 33$, $n/1000$ can only be 32.
    have : n / 1000 = 32 := by omega
    simp [this] at h
    exact h.symm