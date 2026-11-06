import Mathlib

/- Define a sequence of real numbers $ a_1$, $ a_2$, $ a_3$, $ \dots$ by $ a_1 = 1$ and $ a_{n + 1}^3 = 99a_n^3$ for all $ n \ge 1$. Then $ a_{100}$ equals

$ \textbf{(A)}\ 33^{33} \qquad 
\textbf{(B)}\ 33^{99} \qquad 
\textbf{(C)}\ 99^{33} \qquad 
\textbf{(D)}\ 99^{99} \qquad 
\textbf{(E)}\ \text{none of these}$ -/
theorem algebra_87029 (a : ℕ → ℝ) (ha1 : a 1 = 1) (han : ∀ n ≥ 1, (a (n + 1)) ^ 3 = 99 * (a n) ^ 3) :
    a 100 = 99^33 := by
    
    -- All are non-negative.
    have pos : ∀ m : ℕ, 0 ≤ a (m+1) := by 
      intro m
      induction' m with m hm
      simp [ha1]
      by_contra oth; push_neg at oth
      have eq : (a (m+1 + 1)) ^ 3 = 99 * (a (m+1)) ^ 3 := by apply han (m+1); linarith
      have : (a (m+1+1))^3 < 0 := by refine Odd.pow_neg ?_ oth; exact Nat.odd_iff.mpr rfl
      have : 0 ≤ 99 * a (m + 1) ^ 3 := by positivity
      linarith

    -- The expression for the sequence based on the induction formula.
    have lem : ∀ m : ℕ , (a (m+1))^3 = 99^(m) := by
      intro m
      induction' m with m hm
      ring_nf
      simp [ha1]
      have : (a (m+1+1))^3 = 99 * (a (m+1))^3 := by rw [han (m+1) (by linarith)]; 
      rw [this]; rw [hm]; ring_nf
    
    have :(a 100)^3 = 99^99 := by rw [lem 99];
    have :(a 100)^(3:ℝ) = 99 ^ (99:ℝ) := by 
      rify at this; norm_cast; rw [this]; norm_cast
    have a100pos: 0 ≤ a 100  := by
      have : 0 ≤ a (99+1) := pos 99
      ring_nf at this; assumption
    have t1: ((a 100)^(3:ℝ))^(1/(3:ℝ)) = (99^(99:ℝ))^(1/(3:ℝ)) := by rw [this]
    have t2: (a 100) = ((a 100)^(3:ℝ))^(1/(3:ℝ)) := by
      rw [←Real.rpow_mul a100pos 3 (1/(3:ℝ))] 
      ring_nf; field_simp
    rw [t2]; rw [t1]; 
    have : 0 ≤ (99:ℝ) := by linarith 
    rw [←Real.rpow_mul this 99 (1/(3:ℝ))]
    ring_nf 