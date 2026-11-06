import Mathlib

/- Prove that there exists an infinite sequence of perfect squares with the following properties:
(i) The arithmetic mean of any two consecutive terms is a perfect square,
(ii) Every two consecutive terms are coprime,
(iii) The sequence is strictly increasing. -/
theorem number_theory_31417 :
    ∃ f : ℕ → ℕ,
      (∀ n, ∃ m, f n = m ^ 2) ∧
      (∀ n, ∃ k, (f n + f (n + 1)) / 2 = k ^ 2) ∧
      (∀ n, Nat.Coprime (f n) (f (n + 1))) ∧
      StrictMono f := by
  -- **Define the sequence**: We define the sequence ( (s_n) ) by [ s_n = \left((2n+1)^2 - 2\right)^2 \quad \text{for} \quad n \geq 0. ]
  use fun n => if n = 0 then 1 else ((2 * n + 1) ^ 2 - 2)^2
  constructor
  · intro n
    by_cases h : n = 0
    · simp [h] ;use 1 ;simp
    · simp [h]
  -- **Arithmetic mean of consecutive terms**: We need to show that the arithmetic mean of any two consecutive terms is a perfect square. Consider ( s_n ) and ( s_{n+1} ): [ s_n = \left((2n+1)^2 - 2\right)^2 \quad \text{and} \quad s_{n+1} = \left((2n+3)^2 - 2\right)^2. ] The arithmetic mean of ( s_n ) and ( s_{n+1} ) is: [ \frac{s_n + s_{n+1}}{2} = \frac{\left((2n+1)^2 - 2\right)^2 + \left((2n+3)^2 - 2\right)^2}{2}. ] We need to show that this is a perfect square. First, compute ( s_n + s_{n+1} ): [ s_n + s_{n+1} = \left((2n+1)^2 - 2\right)^2 + \left((2n+3)^2 - 2\right)^2. ] Simplify the expressions inside the squares: [ (2n+1)^2 - 2 = 4n^2 + 4n + 1 - 2 = 4n^2 + 4n - 1, ] [ (2n+3)^2 - 2 = 4n^2 + 12n + 9 - 2 = 4n^2 + 12n + 7. ] Therefore, [ s_n + s_{n+1} = (4n^2 + 4n - 1)^2 + (4n^2 + 12n + 7)^2. ] We need to show that: [ \frac{(4n^2 + 4n - 1)^2 + (4n^2 + 12n + 7)^2}{2} ] is a perfect square. Notice that: [ s_n + s_{n+1} = 2\left(4n^2 + 8n + 5\right)^2. ] Thus, [ \frac{s_n + s_{n+1}}{2} = \left(4n^2 + 8n + 5\right)^2, ] which is indeed a perfect square.
  constructor
  · intro n
    use (4 * n ^ 2 + 8 * n + 5)
    by_cases h : n = 0
    · simp [h]
    · simp [h]
      refine Nat.div_eq_of_eq_mul_right ?_ ?_
      simp
      zify
      rw [Nat.cast_sub,Nat.cast_sub]
      simp; ring_nf
      have : 2 ≤ 2 * (n + 1) + 1 := by simp ;nlinarith
      nlinarith
      have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
      nlinarith
  -- **Coprimeness of consecutive terms**: We need to show that ( \gcd(s_n, s_{n+1}) = 1 ). It suffices to show that: [ \gcd\left((2n+1)^2 - 2, (2n+3)^2 - 2\right) = 1. ] Let: [ a = (2n+1)^2 - 2 \quad \text{and} \quad b = (2n+3)^2 - 2. ] Then, [ b - a = (2n+3)^2 - (2n+1)^2 = 8(n+1). ] Therefore, [ \gcd(a, b) = \gcd(a, b - a) = \gcd(a, 8(n+1)). ] Since ( a = (2n+1)^2 - 2 ), we have: [ \gcd((2n+1)^2 - 2, 8(n+1)). ] Notice that: [ \gcd((2(n+1) - 1)^2 - 2, n+1) = \gcd(1^2 - 2, n+1) = \gcd(-1, n+1) = 1. ] Therefore, ( \gcd(s_n, s_{n+1}) = 1 ).
  constructor
  · intro n
    by_cases h : n = 0
    · simp [h]
    simp [h]
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
    have h1 : 2 ≤ (2 * n + 1) ^ 2 := by nlinarith
    have h2 : 2 ≤ (2 * (n + 1) + 1) ^ 2 := by nlinarith
    have h3 : (2 * (n + 1) + 1) ^ 2 - 2 = ((2 * n + 1) ^ 2 - 2) + 8 * (n + 1) := by zify ;rw [Nat.cast_sub h1 ,Nat.cast_sub h2] ;simp ;ring_nf
    rw [h3] ;simp
    have h4 : ((2 * n + 1) ^ 2 - 2).Coprime 8 := by
      have : 8 = 2 ^ 3 := rfl
      have this' : ((2 * n + 1) ^ 2 - 2).Coprime 2 := by 
        refine Nat.coprime_two_right.mpr ?_
        use (2*n^2+2*n-1)
        zify
        rw [Nat.cast_sub,Nat.cast_sub]
        simp ;ring
        nlinarith
        nlinarith
      rw [this]
      exact Nat.Coprime.pow_right 3 this'
    have h5 : ((2 * n + 1) ^ 2 - 2).Coprime (n + 1) := by
      have : 1 + ((2 * n + 1) ^ 2 - 2) = (4*n)*(n+1) := by
        zify
        rw [Nat.cast_sub]
        simp ;ring ;nlinarith
      have : ((2 * n + 1) ^ 2 - 2) = (4*n)*(n+1) - 1:= by omega
      rw [this]
      apply Nat.Coprime.coprime_mul_left_right
      refine (Nat.coprime_self_sub_left ?_).mpr ?_
      nlinarith
      exact Nat.gcd_one_left (4 * n * (n + 1))
    exact Nat.Coprime.mul_right h4 h5
  -- This sequence is clearly strictly increasing because ( (2n+1)^2 - 2 ) is strictly increasing as ( n ) increases.
  refine strictMono_nat_of_lt_succ ?_
  intro n
  by_cases h : n = 0
  · simp [h]
  simp [h]
  zify
  rw [Nat.cast_sub,Nat.cast_sub]
  simp ;ring_nf ;nlinarith
  have : 2 ≤ 2 * (n + 1) + 1 := by simp ;nlinarith
  nlinarith
  have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
  nlinarith
  -- Since all three conditions are satisfied, we have proven the existence of such a sequence.
  
  