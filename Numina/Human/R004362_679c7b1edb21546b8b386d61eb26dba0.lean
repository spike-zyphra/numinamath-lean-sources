import Mathlib

-- Helper function to check if a number x can be written as odd * 2^k
-- def isOddMultipleOf2Power (x : ℕ) (odd : ℕ) : Bool :=
--   if x = 0 then false
--   else if x % 2 = 1 then x = odd
--   else isOddMultipleOf2Power (x / 2) odd


-- Function to extract the odd factor of a natural number
def oddFactor (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 1 then n
  else oddFactor (n / 2)

lemma oddFactor_eq (m k : ℕ) (hm : Odd m) :
  m = oddFactor (2 ^ k * m) := by
  induction' k with k ih
  · -- Base case: k = 0
    simp [pow_zero]
    unfold oddFactor
    split_ifs with h1 h2
    . assumption
    . rfl
    . contrapose h2
      simp
      rw [Nat.odd_iff] at hm
      exact hm

  · -- Inductive step: assume it holds for k, prove it holds for k+1
    rw [pow_succ, mul_comm, ← mul_assoc, mul_comm m  (2 ^ k), oddFactor]
    split_ifs with h1 h2
    . simp at h1
      exact h1
    . have : Even (2 ^ k * m * 2) := by
        use 2 ^ k * m
        ring
      rw [Nat.even_iff] at this
      rw [this] at h2
      simp at h2
    . rw [Nat.mul_div_left]
      . exact ih
      . norm_num


lemma oddFactor_factorization (n : ℕ) (hn : n > 0) :
  ∃ k : ℕ, n = oddFactor n * 2^k := by
  have := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  obtain ⟨k, m, hm, hk⟩ := this
  use k
  rw [hk]
  suffices m = oddFactor (2 ^ k * m) by
    nth_rw 1 [this]
    ring

  exact oddFactor_eq m k hm



/- # Problem:
 What is the maximum number of elements of a subset of $\{1,2, \ldots, 100\}$ such that none of its elements is a multiple of any other?
Inicialmente, observemos que o conjunto $\{51,52,53, \ldots, 100\}$ tem 50 elementos e nenhum de seus elementos é múltiplo de outro. Assim, o subconjunto com o maior número de elementos e que satisfaz a propriedade exigida tem, no mínimo, 50 elementos. Para concluir que 50 é o maior número possível de elementos de um subconjunto que satisfaça a propriedade exigida, basta mostrar que todo subconjunto com mais de 50 elementos possui dois números múltiplos. Para isso, denotamos $B=\{1,2,3, \ldots, 100\}$ e dividimos $B$ em 50 subconjuntos disjuntos, considerando os diversos subconjuntos de $B$ cujos elementos são do tipo número ímpar $\times 2^{k}$, com $k$ natural. Como existem apenas 50 números ímpares entre 1 e 100, obtemos cinquenta subconjuntos dois a dois disjuntos construídos dessa forma, como segue.

- $A_{1}=\{1,2,4,8,16,32,64\}=B \cap\left\{1 \times 2^{k} \mid\right.$ para algum $\left.k=0,1,2,3, \ldots\right\}$;
- $A_{2}=\{3,6,12,24,48,96\}=B \cap\left\{3 \times 2^{k} \mid\right.$ para algum $\left.k=0,1,2,3, \ldots\right\}$;
- $A_{3}=\{5,10,20,40,80\}=B \cap\left\{5 \times 2^{k} \mid\right.$ para algum $\left.k=0,1,2,3, \ldots\right\}$;
- $A_{50}=\{99\}=B \cap\left\{99 \times 2^{k} \mid\right.$ para algum $\left.k=0,1,2,3, \ldots\right\}$.

Observe que $B$ é a união desses cinquenta subconjuntos, isto é,

$$ B=\{1,2, \ldots, 100\}=A_{1} \cup A_{2} \cup \ldots \cup A_{50} $$

e que, se dois elementos de $B$ estiverem num mesmo subconjunto $A_{i}$, então um deles é múltiplo do outro. Assim, se um subconjunto $A$ de $B$ tiver mais do que 50 elementos, podemos afirmar que existem pelo menos dois elementos de $A$ num mesmo subconjunto $A_{i}$ e, portanto, um deles é múltiplo do outro. Isso prova que 50 é o número máximo de elementos de qualquer subconjunto de $B$ que não possua dois elementos tais que um deles seja múltiplo do outro. -/

theorem number_theory_257437 (B : Finset ℕ) (hB : B = Finset.Icc 1 100) :
    IsGreatest {x | ∃ A : Finset ℕ, A ⊆ B ∧ A.card = x ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬(a ∣ b)} 50 := by
  constructor
  . simp [hB]
    use Finset.Icc 51 100
    refine ⟨?_, ?_, ?_⟩
    . intro x hx
      simp at hx ⊢
      omega
    . decide
    . intro a ha b hb hab
      simp at ha hb ⊢
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      interval_cases a
      all_goals interval_cases b
      all_goals try native_decide
      all_goals simp at hab
  . simp [upperBounds, hB]
    intro n A h1 h2 h3
    -- Define the odd factor function that maps each number to its odd factor
    -- If A has more than 50 elements, by the pigeonhole principle, at least one odd number corresponds to two different elements in A

    -- First prove that if n > 50, we will reach a contradiction
    by_contra h_contra
    push_neg at h_contra
    -- h_contra : 50 < n, combined with h2 : A.card = n, gives 50 < A.card

    -- Define the odd set {1, 3, 5, ..., 99}
    let oddSet := (Finset.range 50).map ⟨fun i => 2 * i + 1, fun _ _ h => by simp at h; omega⟩

    -- Prove that oddFactor maps elements of A to oddSet
    have h_maps_to : ∀ a ∈ A, oddFactor a ∈ oddSet := by
      intro a ha
      simp [oddSet]
      -- Here we need to prove that for 1 ≤ a ≤ 100, oddFactor a is an odd number between 1 and 99
      have := h1 ha
      simp at this
      obtain ⟨ha1, ha2⟩ := this
      interval_cases a
      all_goals native_decide

    -- oddSet has 50 elements
    have h_oddSet_card : oddSet.card = 50 := by simp [oddSet]

    -- Apply pigeonhole principle: if A.card > 50 = oddSet.card,
    -- then there exist two different elements in A with the same odd factor
    have h_card_gt : oddSet.card < A.card := by
      rw [h_oddSet_card, h2]
      exact h_contra

    have h_pigeonhole : ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ oddFactor x = oddFactor y := by
      exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card_gt h_maps_to

    -- Derive contradiction from the pigeonhole principle result
    obtain ⟨x, hx_mem, y, hy_mem, hxy, h_eq⟩ := h_pigeonhole

    -- If two numbers have the same odd factor, then one is a multiple of the other
    have h_div : x ∣ y ∨ y ∣ x := by
      have hx : x>0 := by
        have := h1 hx_mem
        simp at this
        omega
      have hy : y>0 := by
        have := h1 hy_mem
        simp at this
        omega
      obtain ⟨k1, hk1⟩ := oddFactor_factorization x hx
      obtain ⟨k2, hk2⟩ := oddFactor_factorization y hy
      -- Now we have x = oddFactor(x) * 2^k1 and y = oddFactor(y) * 2^k2
      -- Since oddFactor(x) = oddFactor(y), we have x = d * 2^k1 and y = d * 2^k2
      rw [h_eq] at hk1
      -- If k1 ≠ k2, then one divides the other
      wlog h : k1 ≤ k2
      ·-- When k2 < k1, prove y ∣ x
        right
        have h_lt : k2 < k1 := by simp at h; exact h
        have : 2^k2 ∣ 2^k1 := by
          rw [Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)]
          exact Nat.le_of_lt h_lt
        obtain ⟨r, hr⟩ := this
        use r
        rw [hk2, hk1, hr]
        ring
      · cases' Nat.eq_or_lt_of_le h with h_eq h_lt
        · -- If k1 = k2, then x = y, contradiction
          subst k1
          rw [← hk2] at hk1
          rw [hk1] at hxy
          simp at hxy
        · -- If k1 < k2, then x ∣ y
          left
          have : 2^k1 ∣ 2^k2 := by
            rw [Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)]
            exact h
          obtain ⟨r, hr⟩ := this
          use r
          rw [hk2, hk1, hr]
          ring

    -- This contradicts h3
    cases h_div with
    | inl h => exact h3 x hx_mem y hy_mem hxy h
    | inr h => exact h3 y hy_mem x hx_mem hxy.symm h
