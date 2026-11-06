import Mathlib

/- Laat $A$ en $B$ positieve gehele getallen zijn.
Definieer de rekenkundige rij $a_{0}, a_{1}, a_{2}, \ldots$ door $a_{n}=A n+B$. Neem aan dat er minstens één $n \geq 0$ is zodat $a_{n}$ een kwadraat is.
$\mathrm{Zij} M$ een positief geheel getal zodat $M^{2}$ het kleinste kwadraat in de rij is. Bewijs dat $ M < A+\sqrt{B}$. -/
theorem number_theory_604245 (A B : ℤ) (hA : A > 0) (hB : B > 0)
    (a : ℕ → ℤ) (ha : ∀ n, a n = A * n + B)
    (h : ∃ n, IsSquare (a n)) :
    ∀M:ℤ, 0 < M → IsLeast {x | ∃n, x = a n ∧ IsSquare x} (M^2) →
    M < A + √B := by
    intro M posM leastM
    -- if M ≤ A, trivial.
    by_cases hMA: M ≤ A
    · rify at hMA hB
      linarith [hMA, Real.sqrt_pos_of_pos hB]
    push_neg at hMA
    rw [IsLeast] at leastM
    -- for M > A, let there be suck k that ak = M^2, or, Ak+B = M^2
    have: ∃ k:ℕ, A*k + B = M^2 := by
      have := leastM.left
      simp [ha] at this
      tauto
    rcases this with ⟨k, hkM⟩
    -- we claim k - (2M-A) < 0.
    have h1: k - (2*M-A) < 0 := by
      by_contra!
      -- otherwise, we consider a_{k-(2M-A)}
      have: a ((k-(2*M-A)).toNat) = (M-A)^2 := by
        rw [ha, Int.toNat_of_nonneg this]
        -- notice that A (k - (2M-A)) + B = (Ak+B) - 2MA + A^2 = M^2-2MA+A^2
        have: A*(k-(2*M-A)) + B = A*k+B -A*(2*M-A) := by ring
        rw [this, hkM]; ring
      -- therefore we obtain a square term. but we suppose M^2 the smallest square term.
      -- contradiction
      replace: M^2 ≤ (M-A)^2 := by
        simp [lowerBounds] at leastM
        rw [← this]
        apply leastM.right _
        use (M-A); rw [this]; ring
      nlinarith [hMA, this]
    -- k-(2M-A)<0 implies (M-A)^2 < B
    have h2: (M-A)^2 < (B:ℝ) := by
      have hh1: A*(k-(2*M-A)) + B < B := by
        simp
        nlinarith [h1, hA]
      -- A(k-(2M-A))+B is exactly (M-A)^2
      have hh2: A*(k-(2*M-A)) + B = (M-A)^2 := by
        have: A*(k-(2*M-A)) + B = A*k+B - A*(2*M-A) := by ring
        rw [this, hkM]; ring
      rw [hh2] at hh1
      rify at hh1; exact hh1
    -- done.
    apply lt_add_of_sub_left_lt ?_
    exact Real.lt_sqrt_of_sq_lt h2