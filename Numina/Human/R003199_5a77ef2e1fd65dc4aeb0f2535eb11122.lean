
import Mathlib

/- # Problem:
 ## Task 23/87

There are prime numbers $p_{i}$ that have the following properties:

1. They are (in decimal notation) truly four-digit.
2. Their digit sum is $Q\left(p_{i}\right)=25$.
3. If you add 4 to them, the result is a "mirror number".

A "mirror number" is a number whose sequence of digits is symmetric with respect to an imaginary central line. Determine all such prime numbers $p_{i}$!
Für die Primzahlen $p_{i}$ gilt nach Eigenschaft 1:

$$ p_{i}=1000 a_{i}+100 b_{i}+10 c_{i}+d_{i} $$

mit $a_{i} ; b_{i} ; c_{i} ; d_{i} \in N, 0 < a_{i} \leq 9,0 \leq b_{i} ; c_{i} ; d_{i} \leq 9$. Als Einerstelle $d_{i}$ einer Primzahl kommen nur die Zahlen $d_{i}=1, d_{2}=3, d_{3}=7$ und $d_{4}=9$ in Frage.

Aus der Eigenschaft 3 folgen $a_{1}=5, a_{2}=7, a_{3}-10=7+4-10=1$ und $a_{4}-10=9+4-10=3$ (der Zehnerübertrag kann sich nicht bis $a_{i}$ fortsetzen, da sonst $a_{3}=0 \mathrm{im}$ Widerspruch zur 1. oder $a_{4}=2, b_{4}=c_{4}=9 \mathrm{im}$ Widerspruch zur 2. Eigenschaft wäre). Damit haben die in Betracht kommenden Zahlen die Gestalt

$$ \begin{aligned} & p_{1}=5000+100 b_{1}+10 c_{1}+1 \\ & p_{2}=7000+100 b_{2}+10 c_{2}+3 \\ & p_{3}=1000+100 b_{3}+10 c_{3}+7 \\ & p_{4}=3000+100 b_{4}+10 c_{4}+9 \end{aligned} $$

Die Möglichkeit $p_{1}$ entfällt, weil aus Eigenschaft 2 folgt, dass $b_{1}+c_{1}=19$ wäre im Widerspruch zu $b_{1}+c_{1} \leq 9+9=18$. Ferner entfällt auch $p_{2}$, weil nach derselben Eigenschaft $b_{2}+c_{2}=15$ sein müsste, aus Eigenschaft 3 aber $b_{2}=c_{2}$ folgt.

Aus Eigenschaft 2 folgt nun $b_{3}+c_{3}=17, b_{4}+c_{4}=13$, und aus Eigenschaft 3 (wegen des Zehnerübertrags) $b_{i}=c_{i}+1$. Damit ist $b_{3}=9, c_{3}=8, p_{3}=1987 ; b_{4}=7, c_{4}=6, p_{4}=3769$.

Tatsächlich sind beide Zahlen Primzahlen.

Zusatz: Streicht man in der Eigenschaft 1 das Wort "echt", so erfüllt auch $p_{i}=0997$ die Bedingungen der Aufgabe. Aus der Eigenschaft 2 kann man leicht weitere Lösungen ausschließen. -/


-- lemma length_eq_three {l : List ℕ} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] :=
--   ⟨fun _ => let [a, b, c] := l; ⟨a, b, c, rfl⟩, fun ⟨_, _, _, e⟩ => e ▸ rfl⟩

lemma list_length_eq_four {l : List ℕ} : l.length = 4 ↔ ∃ a b c d, l = [a, b, c, d] :=
  ⟨fun _ => let [a, b, c, d] := l; ⟨a, b, c, d, rfl⟩, fun ⟨_, _, _, _, e⟩ => e ▸ rfl⟩


theorem number_theory_160897 : {p : ℕ | p.Prime
  ∧ p ∈ Finset.Icc 1000 9999
  ∧ (Nat.digits 10 p).sum = 25
  ∧ ∃ m, p + 4 = m ∧ Nat.digits 10 m = List.reverse (Nat.digits 10 m)}
  = {1987, 3769} := by


  ext p
  simp only [Set.mem_setOf_eq, Finset.mem_Icc]
  constructor
  . intro ⟨h_prime, ⟨h_range1, h_range2⟩, h_sum, ⟨m, hm1, hm2⟩⟩
    by_cases hp1 : 9996 ≤ p
    . interval_cases p
      all_goals simp at h_sum
    . have h_m_length : (Nat.digits 10 m).length = 4 := by
        have := @Nat.le_digits_len_le 10 1000 m (by omega)
        rw [show (Nat.digits 10 1000).length = 4 by norm_num] at this
        have := @Nat.le_digits_len_le 10 m 9999 (by omega)
        rw [show (Nat.digits 10 9999).length = 4 by norm_num] at this
        omega

      have hp1 : p = m - 4 := by omega

      rw [list_length_eq_four] at h_m_length
      obtain ⟨a, b, c, d, hm3⟩ := h_m_length
      rw [hm3] at hm2
      simp at hm2
      obtain ⟨h_a, h_b, h_c, h_d⟩ := hm2
      have hm_eq : m = 1001 * a + 110 * b := by
        rw [← Nat.ofDigits_digits 10 m, hm3]
        rw [h_c, h_d]
        rw [Nat.ofDigits_eq_foldr]
        simp
        ring

      have h_b_range : b < 10 := by
        exact @Nat.digits_lt_base 10 m b (by norm_num) (by rw [hm3]; simp)

      have ⟨h_a_range1, h_a_range2⟩ : 0 < a ∧ a < 10 := by
        constructor
        . by_contra
          have : a = 0 := by omega
          rw [this] at hm_eq
          omega

        . exact @Nat.digits_lt_base 10 m a (by norm_num) (by rw [hm3]; simp)

      interval_cases a
      all_goals interval_cases b
      all_goals simp
      all_goals simp at hm_eq; rw [hm_eq] at hp1; simp at hp1; subst p; try omega
      all_goals contrapose h_sum; simp
      all_goals contrapose h_prime; try native_decide

  . rintro (rfl | rfl)
    all_goals
    . simp
      native_decide
