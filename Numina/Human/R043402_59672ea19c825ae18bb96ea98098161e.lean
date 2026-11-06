import Mathlib

open List

/- Arithmetic sequences $\left(a_n\right)$ and $\left(b_n\right)$ have integer terms with $a_1=b_1=1<a_2 \le b_2$ and $a_n b_n = 2010$ for some $n$. What is the largest possible value of $n$?
$\textbf{(A)}\ 2 \qquad \textbf{(B)}\ 3 \qquad \textbf{(C)}\ 8 \qquad \textbf{(D)}\ 288 \qquad \textbf{(E)}\ 2009$ -/
theorem number_theory_94052 : (∀ (a b : ℕ → ℤ) (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n) (ha1 : a 1 = 1) (hb1 : b 1 = 1)
    (h3 : 1 < a 2) (h4 : a 2 ≤ b 2) (n : ℕ) (h5 : a n * b n = 2010), 
    n ≤ 8)
    ∧ (∃ a b : ℕ → ℤ, (∃ d, ∀ n, a n = a 0 + d * n) ∧ 
    (∃ d, ∀ n, b n = b 0 + d * n) ∧  (a 1 = 1) ∧ (b 1 = 1) ∧ 
    (1 < a 2) ∧ (a 2 ≤ b 2) ∧ a 8 * b 8 = 2010) := by
  constructor
  . intros a b ha hb ha1 hb1 h3 h4 n h5
    -- let $a_n = (n−1)x+1$ and $b_n =(n−1)y+1$ for some $1≤x≤y$.
    obtain ⟨ x, hx ⟩ := ha
    obtain ⟨ y, hy ⟩ := hb
    have ha : ∀ n, a n = (n - 1) * x + 1 := by
      intro m
      nth_rw 2 [← ha1]
      rw [hx, hx 1]
      ring
    have hb : ∀ n, b n = (n - 1) * y + 1 := by
      intro m
      nth_rw 2 [← hb1]
      rw [hy, hy 1]
      ring
    have hx_pos : x ≥ 1 := by 
      rw [← ha1] at h3
      rw [hx 1, hx 2] at h3
      simp at h3
      linarith
    have hy_pos : y ≥ 1 := by
      have : b 1 < b 2 :=
        calc b 1 < a 2 := by rw [hb1]; exact h3
        _ ≤ b 2 := h4
      rw [hy 1, hy 2] at this
      simp at this
      linarith
    have h_x_le_y : x ≤ y := by
      rw [ha, hb] at h4
      simp at h4
      exact h4
    -- x can't be equal to y, since then a_n and b_n would be equal, and 2010 is not a square
    have h_x_neq_y : x ≠ y := by
      by_contra h
      rw [ha, h, ← hb] at h5
      have : ¬IsSquare 2010 := by
        intro h_square
        obtain ⟨ m, h_square ⟩ := h_square
        by_cases hm : m>44
        case pos =>
          apply Nat.succ_le_of_lt at hm
          have : 2010 ≥ 45*45 :=
          calc 2010 = m*m := h_square
            _ ≥ 45*45 := Nat.mul_le_mul hm hm
          simp at this
        case neg =>
          apply Nat.le_of_not_gt at hm
          have : 2010 ≤ 44*44 :=
          calc 2010 = m*m := h_square
            _ ≤ 44*44 := Nat.mul_le_mul hm hm
          simp at this
      apply this
      apply Int.isSquare_natCast_iff.mp
      use (b n)
      rw [h5]
      simp
    have h_two_le_y : 2 ≤ y := by
      apply lt_or_eq_of_le at hy_pos
      cases hy_pos
      case inl h => linarith
      case inr h => 
        exfalso
        apply h_x_neq_y
        rw [← h]
        rw [← h] at h_x_le_y
        apply eq_of_le_of_le
        . exact h_x_le_y
        . exact hx_pos
    have h2010 : 2010 = (n - 1)^2 * x * y + (n - 1) * (x + y) + 1 := calc
      2010 = a n * b n := by rw [h5]
         _ = ((n-1)*x + 1) * ((n-1)*y + 1) := by rw [ha, hb]
         _ = (n - 1)^2 * x * y + (n - 1) * (x + y) + 1 := by ring
    have h2009 : (n-1)*((n-1) * x * y + x + y) = 2009 := by
      suffices : 2009 = (n - 1)^2 * x * y + (n - 1) * (x + y)
      . rw [this]
        ring
      apply (Int.add_left_inj 1).mp h2010
    -- Therefore $n−1$ divides 2009 = 7^2 * 41
    -- split by cases on n to get the divides in the naturals more easily
    cases n
    case zero => simp
    case succ n =>
      have h_dvd : n ∣ 2009 := by
        apply Int.natCast_dvd_natCast.mp
        apply Dvd.intro (n * x * y + x + y)
        simp at h2009
        exact h2009
      have h_primeFactorsList : n.primeFactorsList ∈ (Nat.primeFactorsList 2009).sublists := by
        apply mem_sublists.mpr
        apply Nat.primeFactorsList_sublist_of_dvd
        . apply h_dvd
        . linarith
      have : (Nat.primeFactorsList 2009).sublists = [[], [7], [7], [7, 7], [41], [7, 41], [7, 41], [7, 7, 41]] :=
        calc (Nat.primeFactorsList 2009).sublists = [7,7,41].sublists := by repeat (unfold Nat.primeFactorsList; norm_num)
        [7,7,41].sublists = _ := by
          unfold sublists
          norm_num
      rw [this] at h_primeFactorsList
      simp at h_primeFactorsList

      by_cases h_n_zero : n = 0
      case pos => linarith
      case neg =>
        have hn : n = n.primeFactorsList.prod := by rw [Nat.prod_primeFactorsList h_n_zero]
        rcases h_primeFactorsList with h_empty | h_7 | h_large | h_large | h_large | h_large
        case inl => cases h_empty <;> linarith
        case inr.inl => rw [hn, h_7] ;simp
        -- in the remaining cases, the equasion for h2009 becomes to large
        case inr.inr.inl | inr.inr.inr.inl | inr.inr.inr.inr.inl | inr.inr.inr.inr.inr =>
          rw [h_large] at hn
          simp at hn
          rw [hn] at h2010
          simp at h2010
          exfalso
          have : n^2 * x * y + n * (x + y) + 1 ≥ n^2 * 1 * 2 + n * (1 + 2) + 1 := by
            apply Int.add_le_add_three
            . apply Int.mul_le_mul _ h_two_le_y
              . simp
              . apply Int.mul_nonneg
                . rw [hn]
                  simp
                . linarith
              . apply Int.mul_le_mul <;> try simp
                exact hx_pos
            . apply Int.mul_le_mul <;> try simp
              apply Int.add_le_add hx_pos h_two_le_y
            . simp
          rw [hn] at this
          simp at this
          linarith
  . let a : ℕ → ℤ := fun n => (n-1) * 2 + 1
    let b : ℕ → ℤ := fun n => (n-1) * 19 + 1
    use a
    use b
    constructor
    . use 2
      intro n
      group
    constructor
    . use 19
      intro n
      group
    decide