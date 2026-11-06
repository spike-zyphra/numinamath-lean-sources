import Mathlib
set_option maxHeartbeats 1000000

def is_three_star (n : ℕ) := n ∈ Finset.Icc 100 999 ∧
  ∃ p q r, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ p * q * r = n

/- # Problem:
 We say that a positive three-digit integer is three stars if it is the result of the product of three distinct prime numbers. For example, $286=2 \cdot 11 \cdot 13$ is a three-star number, but $30=2 \cdot 3 \cdot 5$ and $275=5 \cdot 5 \cdot 11$ are not three-star numbers, as the first has only two digits and the second is not the product of three distinct primes.

(a) What is the smallest three-star number?

(b) Show that every three-star number is divisible by 2, by 3, or by 5.
Solução

(a) Podemos fatorar os menores números de três dígitos $100=2 \cdot 2 \cdot 5 \cdot 5,101=101$ (é primo) e $102=2 \cdot 3 \cdot 17$. Como os dois primeiros não são três estrelas, podemos concluir que 102 é o menor número três estrelas.

(b) Se tomarmos um número que é o produto de três primos distintos e que não possua os fatores 2,3 e 5 , ele então será pelo menos $7 \cdot 11 \cdot 13=1001$. Logo, possuirá mais que três dígitos e não será um número três estrelas.

Concluímos assim que todo número três estrelas é divisível por 2, por 3 ou por 5.

#  -/
theorem number_theory_252395 :
    IsLeast {n | is_three_star n} 102 ∧
    ∀ n, is_three_star n → (2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n) := by


  refine ⟨⟨?_, ?_⟩, ?_⟩
  . simp [is_three_star]
    use 2
    refine ⟨by decide, ?_⟩
    use 3
    refine ⟨by decide, ?_⟩
    use 17
    refine ⟨by decide, ?_⟩
    simp
  . simp [is_three_star]
    intro n hn
    obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
    obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr, hn4⟩ := hn3
    by_contra h
    simp at h
    interval_cases n
    . have : Nat.primeFactors 100 = {2, 5} := by
        native_decide
      rw [← hn4] at this
      rw [Nat.primeFactors_mul] at this
      rw [Nat.primeFactors_mul] at this
      rw [Nat.Prime.primeFactors hp] at this
      rw [Nat.Prime.primeFactors hq] at this
      rw [Nat.Prime.primeFactors hr] at this
      have h1: ({2, 5} : Finset ℕ).card = 2 := by native_decide
      rw [← this] at h1
      repeat rw [Finset.card_union] at h1
      rw [show {p} ∩ ({q} :Finset ℕ) = ∅ by
        ext x
        simp
        omega
      ] at h1
      rw [show ({p} ∪ {q}) ∩ ({r} :Finset ℕ) = ∅ by
        ext x
        simp
        omega
      ] at h1
      simp at h1
      
      all_goals by_contra h; rw [h] at hn4; omega


    . have : r = 101 := by
        rw [← Nat.prime_dvd_prime_iff_eq (by assumption) (by decide)]
        use p*q
        rw [← hn4]
        ring
      rw [this] at hn4
      simp at hn4
      obtain ⟨hp1, hq1⟩ := hn4
      rw [hp1, hq1] at hpq
      simp at hpq

  . intro n hn
    unfold is_three_star at hn
    simp at hn
    obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
    obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr, hn4⟩ := hn3

    have hn5: n.primeFactors.card = 3 := by
      rw [← hn4]
      repeat rw [Nat.primeFactors_mul]
      rw [Nat.Prime.primeFactors hp]
      rw [Nat.Prime.primeFactors hq]
      rw [Nat.Prime.primeFactors hr]
      repeat rw [Finset.card_union]

      rw [show {p} ∩ ({q} :Finset ℕ) = ∅ by
        ext x
        simp
        omega
      ]
      rw [show ({p} ∪ {q}) ∩ ({r} :Finset ℕ) = ∅ by
        ext x
        simp
        omega
      ]
      simp
      all_goals by_contra h; rw [h] at hn4; omega

    interval_cases n
    all_goals try native_decide
    all_goals
    . contrapose hn5
      native_decide

