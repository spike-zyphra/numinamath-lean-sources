import Mathlib

/- Trouver tous les couples d'entiers positifs $(m, n)$ tels que $1+(m+n) m$ divise $(m+$ $n)(n+1)-1$. -/
theorem number_theory_607520 (m n : ℤ): (0 ≤ m ∧ 0 ≤ n ∧ 1 + (m + n) * m ∣ (m + n) * (n + 1) - 1) ↔ (m = 0 ∧ 0 ≤ n ∨ m = 1 ∧ 0 ≤ n) := by

  constructor
  · -- Soit $(m, n)$ un couple solution.
    rintro ⟨hm, hn, h⟩
    
    -- Alors $1+(m+n) m$ divise $(m+n)(n+1)-1+$ $1+(m+n) m=(m+n)(m+n+1)$. 
    replace h : 1 + (m + n) * m ∣ (m + n) * (m + n + 1) := by
      have : (m + n) * (m + n + 1) = ( (m + n) * (n + 1) - 1)+ (1 + (m + n) * m) := by ring
      rw [this]
      apply dvd_add
      exact h
      exact dvd_refl _
    
    -- Or, $1+(m+n) m$ est premier avec $m+n$.
    have hco : IsCoprime (1 + (m + n) * m) (m + n) := by
      apply IsCoprime.add_mul_left_left
      apply isCoprime_one_left
    
    -- Ainsi, $1+(m+n) m$ divise $m+n+1$. 
    replace h : 1 + (m + n) * m ∣ m + n + 1 := by
      apply IsCoprime.dvd_of_dvd_mul_left hco
      assumption
    
    -- Donc $m^{2}+m n+1 \leqslant m+n+1$. 
    -- Donc $m=0$ ou $m=1$.
    rw [← or_and_right]
    constructor
    · have := Int.le_of_dvd ?_ h
      by_contra hm'
      push_neg at hm'
      have : 2 ≤ m := by omega
      have : 0 < m + n := by linarith
      have : m + n < (m + n) * m := by nlinarith
      linarith
      linarith
    assumption
    -- Réciproquement, on vérifie que les couples $(0, n)$ et $(1, n)$, où $\boldsymbol{n} \geqslant 0$ est un entier, conviennent.
  · rintro (h|h) <;>
    simp [h]
    use n
    ring
