import Mathlib

set_option maxHeartbeats 400000

/-
1. Find all natural numbers $a, b$, and $c$ that satisfy the equation

$$
\frac{a+b}{a+c}=\frac{b+c}{b+a}
$$

and for which $a b+a c+b c$ is a prime number.
 -/
theorem number_theory_131183 (a b c : ℕ) :
    a + c ≠ 0 ∧ b + a ≠ 0 ∧ ((a + b) / (a + c) : ℚ) = (b + c) / (b + a) ∧
    Nat.Prime (a * b + a * c + b * c) ↔
    (a, b, c) = (1, 1, 1) := by
  constructor
  -- II/1. Označimo praštevilo $a b+b c+c a$ s $p$.
  . let p := a * b + b * c + c * a
    rw [show a * b + a * c + b * c = p by ring]
    rintro ⟨a_add_c_ne_0, b_add_a_ne_0, div_eq, prime_p⟩
    -- Iz zveze dobimo, da je $(a+b)^{2}=c^{2}+p$ oziroma $p=(a+b-c)(a+b+c)$.
    have : (a + b) ^ 2 = c ^ 2 + p := by
      qify at a_add_c_ne_0 b_add_a_ne_0
      field_simp at div_eq
      norm_cast at div_eq
      convert div_eq using 1
      . ring
      . ring
    have eq_in_ℤ : (p : ℤ) = (a + b - c) * (a + b + c) := by
        linarith
    have : (a + b - c : ℤ) ≥ 0 := by
      nlinarith
    have a_add_b_sub_c_eq_in_ℤ : (a + b - c : ℕ) = (a + b - c : ℤ) := by
      omega
    have p_eq_mul : p = (a + b - c) * (a + b + c) := by
      zify
      rw [a_add_b_sub_c_eq_in_ℤ]
      exact eq_in_ℤ
    -- Ker je $p$ praštevilo in je $0 < a+b-c < a+b+c$, mora biti $a+b-c=1$ in $a+b+c=p$ oziroma $c=\frac{p-1}{2}$ in $a+b=\frac{p+1}{2}$.
    have : a + b - c ≤ a + b + c := by
      omega
    have : a + b - c = 1 ∧ a + b + c = p := by
      have := by
        rw [p_eq_mul] at prime_p
        exact Nat.prime_mul_iff.mp prime_p
      rcases this with ⟨_, eq_1⟩ | ⟨_, eq_1⟩
      . exfalso
        have : a + b - c = p := by
          nlinarith
        have : p > 1 := by
          exact Nat.Prime.one_lt prime_p
        linarith
      . --omega
        constructor
        . exact eq_1
        . nlinarith
    have : c = ((p - 1) / 2 : ℚ) ∧ a + b = ((p + 1) / 2 : ℚ) := by
      zify at this
      rw [a_add_b_sub_c_eq_in_ℤ] at this
      qify at this
      --rcases this
      constructor
      . linarith
      . linarith
    rcases this with ⟨c_eq, a_add_b_eq⟩
    -- Po drugi strani pa mora biti $a b=p-b c-c a=p-c(a+b)=p-\frac{p-1}{2} \cdot \frac{p+1}{2}=-\frac{p^{2}-4 p-1}{4}$ pozitivno število.
    have a_b_eq : a * b = (- (p ^ 2 - 4 * p - 1) / 4 : ℚ) := by
      have : a * b = (p - c * (a + b) : ℤ) := by
        unfold p
        push_cast
        ring
      qify at this
      nlinarith
    -- nonnegativity should suffice
    have : (p ^ 2 - 4 * p - 1 : ℤ) ≤ 0 := by
      have : a * b ≥ 0 := by simp
      qify at this
      rw [a_b_eq] at this
      qify
      linarith
    -- Ničli kvadratne funkcije $f(x)=x^{2}-4 x-1$, ki ima pozitiven vodilni koeficient, sta $2-\sqrt{5}$ in $2+\sqrt{5} < 5$, torej je $p$ lahko le 2 ali 3.
    have : p < 5 := by
      by_contra p_ge_5
      have : (p ^ 2 - 4 * p - 1 : ℤ) ≥ 1 := by
        nlinarith
      linarith
    have : p ∈ (Finset.range 5).filter Nat.Prime := by
      simp
      exact And.symm ⟨prime_p, this⟩
    generalize p_eq : p = p at this
    fin_cases this
    . -- Ker 2 ne more biti, saj $c=\frac{p-1}{2}$ ne bi bilo celo s̆tevilo, je $p=3$.
      exfalso
      norm_num [p_eq] at c_eq
      have : 2 * c = 1 := by
        linarith
      simp at this --omega
    . -- Tako je $c=1, a+b=2$ in ker sta $a$ in $b$ naravni števili, je edina rešitev $a=b=c=1$.
      -- Trojica $(1,1,1)$ seveda ustreza vsem pogojem naloge.
      norm_num [p_eq] at c_eq a_add_b_eq
      unfold p at p_eq
      --have : a * b = 1 := by nlinarith
      have : a = 1 := by nlinarith
      have : b = 1 := by linarith
      simp
      omega
  . rintro ⟨rfl, rfl, rfl⟩
    native_decide
