import Mathlib

/- Laat $A$ een verzameling van positieve gehele getallen zijn met de volgende eigenschap: voor elk positief geheel getal $n$ zit precies één van de drie getallen $n, 2 n$ en $3 n$ in $A$. Verder is gegeven dat $2 \in A$. Bewijs dat $13824 \notin A$. -/
theorem number_theory_604814 (A : Set ℕ) (hApos : ∀ n ∈ A, n > 0)(hA : ∀ n, 0 < n → (n ∈ A ∨ 2 * n ∈ A ∨ 3 * n ∈ A))
    (hA' : ∀ n, 0 < n → ¬(n ∈ A ∧ 2 * n ∈ A)) (hA'' : ∀ n, 0 < n → ¬(n ∈ A ∧ 3 * n ∈ A))
    (hA''' : ∀ n, 0 < n → ¬(2 * n ∈ A ∧ 3 * n ∈ A)) (hA'''' : 2 ∈ A) :
    ¬(13824 ∈ A) := by
      -- We prove the following two claims: (i) If $m \\in A$ with $2 \\mid m$, then 6 * m ∈ A
      have h1 : ∀ m ∈ A, 2 ∣ m → 6 * m ∈ A := by
        -- First, claim (i). Assume that $m \\in A$ with $2 \\mid m$
        intro m hm hdvd
        --  By choosing $n=m$, we see that $2 m$ and $3 m$ are not in $A$
        have : ¬ 3 * m ∈ A := by
          have h := hA'' m (hApos m hm)
          simp at h
          apply h hm
        have : ¬ 9 * m ∈ A := by
          let n := m / 2
          have heq : m = 2 * n := by
            unfold n
            exact (Nat.div_eq_iff_eq_mul_right (hApos 2 hA'''') hdvd).mp rfl
          have hnpos : n > 0 := by exact (Nat.lt_div_iff_mul_lt' hdvd 0).mpr (hApos m hm)
          -- By choosing $n=\\frac{m}{2}$, we see that $\\frac{m}{2}$ and $\\frac{3}{2} m$ are not in $A$.
          have := hA' n (by unfold n; exact hnpos)
          have hn : ¬ n ∈ A := by
            intro hnin
            apply this ⟨hnin, (by rw [heq] at hm; exact hm)⟩
          have := hA''' n (by unfold n;  exact hnpos)
          have h3n : ¬ 3 * n ∈ A := by
            intro h3nin
            apply this ⟨(by rw [heq] at hm; exact hm), h3nin⟩
          -- If we now consider $n=\\frac{3}{2} m$, then $2 n=3 m$ is not in $A$ and $n=\\frac{3}{2} m$ itself is also not in $A$, so $3 n=\\frac{9}{2} m$ is. With $n=\\frac{9}{2} m$, we now see that $9 m \\notin A$.
          have := hA (3 * n) (by linarith)
          rcases this with h1 | h2 | h3
          · contradiction
          · nth_rw 2 [mul_comm] at h2
            rw [← mul_assoc, ← heq, mul_comm] at h2
            contradiction
          · ring_nf at h3
            have := hA' (n * 9) (by linarith)
            simp at this
            rw [← mul_assoc, ← heq] at this
            nth_rw 2 [mul_comm] at this
            apply this h3
        --  Finally, consider $n=3 m$: we know that $3 m \\notin A$ and $9 m \\notin A$, so $6 m \\in A$.
        have := hA (3 * m) (by exact Nat.succ_mul_pos 2 (hApos m hm))
        rcases this with h1 | h2 | h3
        · contradiction
        · ring_nf at h2
          rw [mul_comm] at h2
          exact h2
        · ring_nf at h3
          rw [mul_comm] at h3
          contradiction
      -- (ii) If $m \\in A$ with $3 \\mid m$, then \\frac{4}{3} m ∈ A
      have h2 : ∀ m ∈ A, 3 ∣ m → 4 * (m / 3) ∈ A := by
        -- Now, claim (ii). Assume that $m \\in A$ with $3 \\mid m$.
        intro m hm hdvd
        let n := m / 3
        have heq : m = 3 * n := by exact Eq.symm (Nat.mul_div_cancel' hdvd)
        have hnpos : n > 0 := by exact (Nat.lt_div_iff_mul_lt' hdvd 0).mpr (hApos m hm)
        -- By choosing $n=m$, we see that $2 m$ is not in $A$.
        have h2m : ¬ 2 * m ∈ A := by
          have := hA' m (by exact hApos m hm)
          simp at this
          apply this hm
        -- By choosing $n=\\frac{m}{3}$, we see that $\\frac{m}{3}$ and $\\frac{2}{3} m$ are not in $A$
        have h2n : ¬ 2 * n ∈ A := by
          have := hA''' n hnpos
          intro h2n
          apply this ⟨h2n, (by rw [heq] at hm; exact hm)⟩
        -- If we now choose $n=\\frac{2}{3} m$, then $n$ and $3 n$ are not in $A$, so $2 n=\\frac{4}{3} m$ is. This proves claim (ii).
        have := hA (2 * n) (by linarith)
        rcases this with h1 | h2 | h3
        · contradiction
        · ring_nf at h2
          have : m / 3 = n := by unfold n; exact rfl
          rw [this, mul_comm]
          exact h2
        · rw [heq] at h2m
          ring_nf at h2m
          ring_nf at h3
          contradiction
      -- We know that $2 \\in A$. By repeatedly applying claims (i) and (ii), we can show that the following numbers are all in $A$: $$ 2 \\xrightarrow{\\text { (i) }} 2^{2} \\cdot 3 \\xrightarrow{\\text { (i) }} 2^{3} \\cdot 3^{2} \\xrightarrow{\\text { (i) }} 2^{4} \\cdot 3^{3} \\xrightarrow{\\text { (i) }} 2^{5} \\cdot 3^{4} \\xrightarrow{\\text { (ii) }} 2^{7} \\cdot 3^{3} \\xrightarrow{\\text { (ii) }} 2^{9} \\cdot 3^{2} . $$Since $2^{9} \\cdot 3^{2} \\in A$, it follows that $2^{9} \\cdot 3^{3} \\notin A$. Since $13824=2^{9} \\cdot 3^{3}$, this is what we needed to prove.
      have : 12 ∈ A := by apply h1 2  hA'''' (by norm_num)
      have : 72 ∈ A := by apply h1 12 this (by norm_num)
      have : 432 ∈ A := by apply h1 72 this (by norm_num)
      have : 2592 ∈ A := by apply h1 432 this (by norm_num)
      have : 3456 ∈ A := by apply h2 2592 this (by norm_num)
      have : 4608 ∈ A := by apply h2 3456 this (by norm_num)
      have h := hA'' 4608 (by linarith)
      simp at h
      apply h this
