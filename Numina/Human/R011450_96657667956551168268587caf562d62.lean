import Mathlib

namespace number_theory_251699

abbrev AdjacentCondition a b := a = 2 * b ∨ a - b = 1 ∨ a - b = 2

/- In a circle, 99 natural numbers are written. If $a$ and $b$ are two adjacent numbers on the circle, then $\frac{a}{b}=2$, $a-b=1$ or $a-b=2$. Prove that there exists some number on the circle that is divisible by 3. -/
theorem number_theory_251699 (a : Fin 99 → ℕ)
    (h : ∀ i, AdjacentCondition (a i) (a (i + 1)) ∨ AdjacentCondition (a (i + 1)) (a i)) :
    ∃ i, 3 ∣ a i := by
  /-
  Solution

  Let $a_{1}, a_{2}, \ldots, a_{99}$ be the numbers on the circle, written in order, and suppose, by contradiction, that none of them is a multiple of 3. Hence, if two neighbors $a$ and $b$ leave the same remainder when divided by 3, since 3 cannot divide the differences 1 and 2, it follows that $a=2 b$ or $b=2 a$. Knowing that 3 divides $a-b$, in both previous situations we could conclude that one of them, and therefore both, must be a multiple of 3. This contradicts our initial assumption. Since $a$ and $b$ are not multiples of 3 and their remainders are distinct, one of them must leave a remainder of 1 and the other must leave a remainder of 2 when divided by 3. This tells us that $a_{i}+a_{i+1}$ is a multiple of 3 for all $i \leq 98$. We can write:

  $$ \begin{aligned} & S=\left(a_{1}+a_{2}\right)+\ldots+\left(a_{97}+a_{98}\right)+a_{99} \ & S=a_{1}+\left(a_{2}+a_{3}\right)+\ldots+\left(a_{98}+a_{99}\right) \end{aligned} $$
   -/
  by_contra neg_3_dvd
  push_neg at neg_3_dvd
  -- adapted to a simpler way to prove in Lean than the solution text above
  let a_fin i := (a i : Fin 3)
  let Eq_1_or_2_Fin_3 m n := let m_fin := (m : Fin 3); let n_fin := (n : Fin 3); m_fin = 1 ∧ n_fin = 2 ∨ m_fin = 2 ∧ n_fin = 1
  have {m n} : AdjacentCondition m n → ¬ 3 ∣ m → ¬ 3 ∣ n → Eq_1_or_2_Fin_3 m n := by
    unfold Eq_1_or_2_Fin_3
    intro adj neg_3_dvd_m neg_3_dvd_n m_fin n_fin
    unfold AdjacentCondition at adj
    replace adj : m_fin = 2 * n_fin ∨ m_fin = n_fin + 1 ∨ m_fin = n_fin + 2 := by
      simp [m_fin, n_fin]
      rcases adj with h | h | h
      . left
        norm_cast
        congr --exact congrArg Nat.cast h
      . right; left
        have : m = n + 1 := by omega
        norm_cast
        congr
      . right; right
        have : m = n + 2 := by omega
        norm_cast
        congr
    have m_fin_ne_0 : m_fin ≠ 0 := by
      simp [m_fin]
      exact neg_3_dvd_m
    clear neg_3_dvd_m
    have n_fin_ne_0 : n_fin ≠ 0 := by
      simp [n_fin]
      exact neg_3_dvd_n
    clear neg_3_dvd_n
    generalize m_fin_eq : m_fin = m_fin'
    fin_cases m_fin'
    . --simp at m_fin_eq ⊢
      contradiction
    . --simp at m_fin_eq ⊢
      omega
    . omega
  have {m n} : AdjacentCondition m n ∨ AdjacentCondition n m → ¬ 3 ∣ m → ¬ 3 ∣ n → Eq_1_or_2_Fin_3 m n := by
    intro adjs neg_3_dvd_m neg_3_dvd_n
    rcases adjs with adj | adj
    . exact this adj neg_3_dvd_m neg_3_dvd_n
    . have := this adj neg_3_dvd_n neg_3_dvd_m
      unfold Eq_1_or_2_Fin_3 at this ⊢
      omega
  --have : ∀ i, 3 ∣ (a i + a (i + 1)) := by
  --have a_fin_repeating : ∀ i, ∃ m n, m ≠ n ∧ a_fin i = m ∧ a_fin (i + 1) = n /- This doesn't contain enough information for the subsequent proofs. -/ := by
  have a_fin_repeating i : a_fin i = 1 ∧ a_fin (i + 1) = 2 ∨ a_fin i = 2 ∧ a_fin (i + 1) = 1 :=
    this (h i) (neg_3_dvd i) (neg_3_dvd (i + 1))
  /-
  Since the sums in each parenthesis are multiples of 3, we can conclude that $a_{1}$ and $a_{99}$ leave the same remainder when divided by 3. However, this is a contradiction, because neighboring numbers do not leave the same remainder when divided by 3. This tells us that the initial assumption is false and, consequently, at least one of them must be a multiple of 3.

  #
   -/
  -- adapted to a simpler way to prove in Lean than the solution text above
  --have : ∀ i, a i ≡ a (i + 2) [MOD 3] := by
  have : a_fin.Periodic 2 := by
    intro i
    have h_a_i := a_fin_repeating i
    have h_a_i_add_1 := a_fin_repeating (i + 1)
    rw [show i + 1 + 1 = i + 2 by ring] at h_a_i_add_1
    cases h_a_i <;>
    . cases h_a_i_add_1 <;>
      . omega
  --have : ∀ n, a 0 ≡ a (2 * n) [MOD 3] := by
  have : ∀ (n : ℕ), a_fin.Periodic (n * 2) :=
    this.nat_mul
  specialize this 50 0
  simp at this
  symm at this
  --have : ¬ a 0 ≡ a 1 [MOD 3] /- a 0 ≢ a 1 [MOD 3] -/ :=
  have : a_fin 0 ≠ a_fin 1 := by
    specialize a_fin_repeating 0
    simp at a_fin_repeating
    /-
    rcases a_fin_repeating with ⟨a_fin_0_eq, a_fin_1_eq⟩ | ⟨a_fin_0_eq, a_fin_1_eq⟩
    . rw [a_fin_0_eq, a_fin_1_eq]
     -/
    cases a_fin_repeating <;>
    . omega
  contradiction

end number_theory_251699
open number_theory_251699
