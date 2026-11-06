import Mathlib

/-
## Task B-3.4.

Determine all pairs of natural numbers $a$ and $b$ such that $a^{2}-4 b^{2}=a-2 b+2^{2022}$.
 -/
theorem algebra_246931 (a b : ℕ) :
    (a^2 - 4 * b^2 : ℤ) = a - 2 * b + 2^2022 ↔ a = 2^2021 + 1 ∧ b = 2^2020 := by
  -- ## Rješenje.
  constructor
  . intro eq
    -- Danu jednadžbu možemo zapisati u obliku $(a-2 b)(a+2 b-1)=2^{2022}$, odakle slijedi da je $a+2 b-1=2^{x}$ i $a-2 b=2^{y}$, pri čemu su $x$ i $y$ nenegativni cijeli brojevi.
    have mul_eq : ((a - 2 * b) * (a + 2 * b - 1) : ℤ) = 2 ^ 2022 := by
      linarith
    /- not needed
    have : (2 ^ 2022 : ℤ) ≥ 0 := by
      linarith
     -/
    have : (a + 2 * b - 1 : ℤ) ≥ 0 := by
      by_contra not_nonneg
      simp at not_nonneg
      have : a = 0 := by
        omega
      rw [this] at mul_eq
      have : b = 0 := by
        omega
      rw [this] at mul_eq
      norm_num at mul_eq --conv_lhs at mul_eq => norm_num --omega
    have : (a - 2 * b : ℤ) ≥ 0 := by
      nlinarith
    let left := (a - 2 * b : ℤ).toNat
    let right := (a + 2 * b - 1 : ℤ).toNat
    replace mul_eq : left * right = 2 ^ 2022 := by
      unfold left right
      zify
      have : (a - 2 * b : ℤ).toNat = (a - 2 * b : ℤ) := by
        omega
      rw [this]
      have : (a + 2 * b - 1 : ℤ).toNat = (a + 2 * b - 1 : ℤ) := by
        omega
      rw [this]
      exact mul_eq
    have prime_two := Nat.prime_two
    have : ∃ x ≤ 2022, right = 2 ^ x := by
      have : right ∣ 2 ^ 2022 := by
        generalize h : 2 ^ 2022 = m
        rw [h] at mul_eq
        clear h
        exact Dvd.intro_left left mul_eq
      generalize h : 2022 = n
      rw [h] at this
      clear h mul_eq
      exact (Nat.dvd_prime_pow prime_two).mp this
    rcases this with ⟨x, x_le, right_eq⟩
    have : ∃ y ≤ 2022, left = 2 ^ y := by
      have : left ∣ 2 ^ 2022 := by
        generalize h : 2 ^ 2022 = m
        rw [h] at mul_eq
        clear h
        exact Dvd.intro right mul_eq
      exact (Nat.dvd_prime_pow prime_two).mp this
    rcases this with ⟨y, y_le, left_eq⟩
    -- Nadalje, kako su $a$ i $b$ prirodni brojevi, očito je $a+2 b-1>a-2 b$, tj. $x>y \geqslant 0$.
    have : right > left := by
      unfold left right
      suffices (a + 2 * b - 1 : ℤ) > (a - 2 * b : ℤ) by
        omega
      have : b ≥ 1 := by
        have : b ≠ 0 := by
          intro b_eq_0
          unfold left right at mul_eq
          conv_lhs at mul_eq => norm_num [b_eq_0]
          /-
          have : (a - 1 : ℤ) = (a - 1 : ℕ) := by
            omega
          rw [this] at mul_eq
           -/
          have : a * (a - 1) = 2 ^ 2022 := by
            linarith
          /-
          have : a - 1 < a := by
            linarith
           -/
          have : (a - 1) ^ 2 < 2 ^ 2022 := by
            nlinarith
          have : a - 1 < 2 ^ 1011 := by
            nlinarith
          have : a ^ 2 > 2 ^ 2022 := by
            nlinarith
          have : a > 2 ^ 1011 := by
            nlinarith
          omega
        omega
      nlinarith
    have : x > y := by
      have : 2 ^ x > 2 ^ y := by
        linarith
      have _2_gt_1 : 2 > 1 :=
        by simp
      exact (Nat.pow_lt_pow_iff_right _2_gt_1).mp this
    -- Nadalje, kako je $2^{x}+2^{y}=a+2 b-1+a-2 b=2 a-1$ neparan broj mora vrijediti $y=0$, tj. $a-2 b=1$.
    have : 2 ^ x + 2 ^ y = 2 * a - 1 := by
      omega
    have : y = 0 := by
      by_contra y_ne_0
      have : y ≥ 1 := by
        omega
      have : x ≥ 1 := by
        omega
      have : 2 ∣ 2 ^ x + 2 ^ y := by
        have : 2 ^ x + 2 ^ y = 2 * (2 ^ (x - 1) + 2 ^ (y - 1)) := by
          conv_lhs =>
            rw [show x = x - 1 + 1 by omega]
            rw [show y = y - 1 + 1 by omega]
          ring
        rw [this]
        omega
      /-
      have : ¬ 2 ∣ 2 * a - 1 := by
        omega
       -/
      omega
    have /- left_eq -/ : left = 1 := by
      rw [this] at left_eq
      exact left_eq
    -- Iz $y=0$ slijedi da je $x=2022$.
    /-
    Dakle, dobivamo sustav

    $$ \left{\begin{array}{l} a+2 b-1=2^{2022} \ a-2 b=1 \end{array}\right. $$
    -/
    have /- right_eq -/ : right = 2 ^ 2022 := by
      --rw [this] at mul_eq
      nlinarith
    -- Rješavanjem dobivenog sustava nalazimo $a=2^{2021}+1$ i $b=2^{2020}$.
    omega
  . rintro ⟨a_eq, b_eq⟩
    rw [a_eq, b_eq]
    ring
