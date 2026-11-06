import Mathlib
/- C1. For a positive integer $n$, if we multiply all numbers from 1 to $n$ together, we denote the result as $n$ ! ('$n$ factorial'). For example, $5 !=1 \cdot 2 \cdot 3 \cdot 4 \cdot 5=120$.

(a) Find all integers $n$ with $1 \leqslant n \leqslant 100$ such that $n ! \cdot (n+1)$ ! is the square of an integer. Also provide a proof that you have found all such numbers.

(b) Prove that for no positive integer $n$ does $n$ ! $\cdot (n+1) ! \cdot (n+2) ! \cdot (n+3)$ ! equal the square of an integer. -/
theorem number_theory_171558_1 :
    {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ IsSquare (Nat.factorial n * Nat.factorial (n + 1))} =
    {3,8,15,24,35,48,63,80,99} := by
  ext n
  simp
  -- We note that (n+1)! = (n+1)⋅n!. Therefore, we see that n!⋅(n+1)! =(n!)^2 ⋅(n+1).
  -- Since (n!)^2 is itself a square, this product is a square precisely when n+1 is a square.
  have h_sq : IsSquare (n+1) ↔ IsSquare (Nat.factorial n * Nat.factorial (n + 1)) := by
    constructor
    case mp =>
      intro h
      obtain ⟨k, h_k⟩ := h
      use k*n.factorial
      rw [Nat.factorial_succ, h_k]
      ring
    case mpr =>
      unfold IsSquare
      qify
      intro h
      rw [Nat.factorial_succ] at h
      obtain ⟨k, h_k⟩ := h
      use k/n.factorial
      have : n.factorial ∣ k := by
        apply (Nat.pow_dvd_pow_iff two_ne_zero).mp
        rw [pow_two, pow_two]
        use n+1
        qify
        rw [← h_k]
        simp
        group
      rw [Rat.natCast_div k n.factorial this]
      group
      norm_cast
      rw [pow_two]
      simp
      rw [← h_k]
      simp
      have (a b:ℚ) (h_pos:a≠0) : a * (b*a) * (a ^ 2)⁻¹ = b :=
        calc a * (b*a) * (a ^ 2)⁻¹ = a * b * a * (a ^ 2)⁻¹ := by group
        _ = b * (a ^ 2) * (a ^ 2)⁻¹ := by group
        _ = b := by
          rw [mul_assoc, Rat.mul_inv_cancel]
          group
          case a =>
            intro h
            apply h_pos
            apply eq_zero_of_zpow_eq_zero h
      rw [← this (n.factorial:ℚ) (1 + (n:ℚ)) ?pos]
      group
      case pos =>
        intro h
        simp at h
        apply Nat.factorial_ne_zero n
        trivial
  -- For 1⩽n⩽100, (n+1) is a square for n=3,8,15,24,35,48,63,80,99
  constructor
  case mp =>
    intros h
    obtain ⟨ h_low, h_high, h_IsSquare⟩ := h
    apply h_sq.mpr at h_IsSquare
    obtain ⟨k, h_IsSquare⟩ := h_IsSquare
    have : k < 11 := by
      by_contra h
      simp at h
      have : n + 1 ≥ 121 := calc
        n + 1 = k * k := h_IsSquare
        _ ≥ 11*11 := Nat.mul_le_mul h h
      linarith
    interval_cases k <;> simp at h_IsSquare <;> rw [h_IsSquare] <;> try trivial
    linarith
  case mpr =>
    intro h
    constructor ; omega
    constructor ; omega
    apply h_sq.mp
    rcases h with h|h|h|h|h|h|h|h|h <;> rw [h]
    . use 2
    . use 3
    . use 4
    . use 5
    . use 6
    . use 7
    . use 8
    . use 9
    . use 10

theorem number_theory_171558_2 (n:ℕ) :
    ¬ IsSquare (Nat.factorial n * Nat.factorial (n+1) * Nat.factorial (n+2)  * Nat.factorial (n+3)) := by
  intro h
  have : IsSquare ((n+1) * (n+3)) := by
    revert h
    unfold IsSquare
    qify
    intro h
    obtain ⟨k, h⟩ := h
    -- We rewrite the product n!⋅(n+1)!⋅(n+2)!⋅(n+3)! as: (n!)^2⋅(n+1)⋅(n+2)!⋅(n+3)! = (n!)^2 ⋅(n+1)⋅((n+2)!)^2 ⋅(n+3).
    have : (k:ℚ)^2 = (n+1) * (n+3) * ((n+2).factorial^2) * (↑n.factorial^2) := by
      calc (k:ℚ)^2 = k*k := pow_two (k:ℚ)
        _ = ↑n.factorial * ↑(n + 1).factorial * ↑(n + 2).factorial * ↑(n + 3).factorial := by rw [h]
        _ = ↑n.factorial * ((↑n+1) * ↑n.factorial) * ↑(n + 2).factorial * ((↑n+3) * ↑(n + 2).factorial) := by
          rw [Nat.factorial_succ n, Nat.factorial_succ (n+2)]
          norm_cast
        _ = _ := by group
    -- Since (n!)^2 and ((n+2)!)^2 are both squares, this product is a square precisely when (n+1)(n+3) is a square.
    use k/(n.factorial * (n+2).factorial)
    have h_div : (n.factorial * (n+2).factorial) ∣ k := by
      apply (Nat.pow_dvd_pow_iff two_ne_zero).mp
      use (n+1)*(n+3)
      qify
      rw [this]
      calc ((n:ℚ) + 1) * (↑n + 3) * ↑(n + 2).factorial ^ 2 * ↑n.factorial ^ 2
          = ((↑n + 1) * (↑n + 3)) * ↑(n + 2).factorial ^ 2 * ↑n.factorial ^ 2 := by rw [mul_assoc]
        _ = ↑(n + 2).factorial ^ 2 * ↑n.factorial ^ 2 * ((↑n + 1) * (↑n + 3)) := by group
        _ = ↑n.factorial ^ 2 * ↑(n + 2).factorial ^ 2 * ((↑n + 1) * (↑n + 3)) := by group
        _ = (↑n.factorial * ↑(n + 2).factorial) ^ 2 * ((↑n + 1) * (↑n + 3)) := by rw [mul_pow]
    rw [Rat.natCast_div _ _ h_div]
    simp
    ring_nf
    rw [this]
    simp
    have h_pos (num:ℕ): (num.factorial :ℚ)^2 ≠ 0 := by
      norm_cast
      intro h
      apply sq_eq_zero_iff.mp at h
      apply Nat.factorial_ne_zero
      exact h
    rw [add_comm 2 n]
    rw [mul_inv_cancel_right₀ (h_pos n)]
    rw [mul_inv_cancel_right₀ (h_pos (n+2))]
    group
  -- We show that (n+1)(n+3) cannot be a square. Suppose that (n+1)(n+3)=k^2 were a square.
  obtain ⟨k,h_IsSquare⟩ := this
  -- Since (n+1)^2<(n+1)(n+3)<(n+3)^2 , it would have to be that n+1<k<n+3, or equivalently k=n+2.
  have h_lower_bound : n+1 < k := by
    have h_pos : 2 ≠ 0 := by trivial
    apply (Nat.pow_lt_pow_iff_left h_pos).mp
    calc (n+1)^2
        = (n+1)*(n+1) := by rw [pow_two]
      _ < (n+1)*(n+3) := by apply Nat.mul_lt_mul_of_pos_left <;> simp
      _ = k^2 := by rw [h_IsSquare, pow_two]
  have h_upper_bound : k < n+3 := by
    have h_pos : 2 ≠ 0 := by trivial
    apply (Nat.pow_lt_pow_iff_left h_pos).mp
    calc (n+3)^2
        = (n+3)*(n+3) := by rw [pow_two]
      _ > (n+1)*(n+3) := by apply Nat.mul_lt_mul_of_pos_right <;> simp
      _ = k^2 := by rw [h_IsSquare, pow_two]
  have h_eq : k = n+2 := by linarith
  -- This is not possible, because (n+1)(n+3)=(n+2)^2 −1 and that is not equal to (n+2)^2 .
  subst k
  revert h_IsSquare
  ring_nf
  simp