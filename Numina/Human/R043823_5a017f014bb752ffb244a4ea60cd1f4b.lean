import Mathlib

def is_practical (n : ℕ) := ∀ m ≤ n, ∃ s : Finset ℕ, m = ∑ d ∈ s, d ∧ s ⊆ Nat.divisors n

/- Call a positive integer $n$ practical if every positive integer less than or equal to $n$ can be written as the sum of distinct divisors of $n$.

For example, the divisors of 6 are $\mathbf{1 , 2}, \mathbf{3}$, and $\mathbf{6}$. Since

$$
1=\mathbf{1}, \quad 2=\mathbf{2}, \quad 3=\mathbf{3}, \quad 4=\mathbf{1}+\mathbf{3}, \quad 5=\mathbf{2}+\mathbf{3}, \quad 6=\mathbf{6},
$$

we see that 6 is practical.

Prove that the product of two practical numbers is also practical. -/
theorem number_theory_604767 :
    ∀ m n, m > 0 → n > 0 → is_practical m → is_practical n → is_practical (m * n) := by

  intro p q hpPos hqPos hpPrac hqPrac

  unfold is_practical

  intro k hk

  -- With k ≤ p * q, we can write k = a * q + b with 0 ≤ a ≤ p, and 0 ≤ b < q.
  have : ∃ a b : ℕ, a ≤ p ∧ b < q ∧ k = a * q + b := by
    use k / q
    use k % q
    constructor
    . apply Nat.div_le_of_le_mul
      linarith
    . constructor
      . exact Nat.mod_lt k hqPos
      . exact Eq.symm (Nat.div_add_mod' k q)

  obtain ⟨ a, b, ⟨ ha, hb, hab ⟩  ⟩ := this

  unfold is_practical at hpPrac hqPrac

  -- Let sa be the set of divisors of p that add up to a.
  obtain hpPrac_a := hpPrac a ha
  obtain ⟨ sa, hsa ⟩ := hpPrac_a

  -- Let sb be the set of divisors of q that add up to b.
  obtain hpPrac_b := hqPrac b (Nat.le_of_lt hb)
  obtain ⟨ sb, hsb ⟩ := hpPrac_b

  -- Define an embedding f_emb from x to q * x.
  let f := fun x ↦ q * x
  have f_inj : Function.Injective f := by apply mul_right_injective₀; exact Nat.not_eq_zero_of_lt hqPos
  let f_emb : Function.Embedding ℕ ℕ := ⟨ f, f_inj ⟩

  -- Take the range of f_emb over sa.
  let saq := sa.map f_emb

  -- Then saq and sb are distjoint.
  have disj : Disjoint saq sb := by
    rw [@Finset.disjoint_iff_ne]
    intro cq hcq
    intro d hd
    have : d < cq := by
      calc
        d ≤ b := by rw [hsb.left]
                    have : {d} ⊆ sb := by exact Finset.singleton_subset_iff.mpr hd
                    apply Finset.sum_le_sum_of_subset this
        b < q := by exact hb
        _ ≤ cq  := by
          simp [saq, f_emb, f] at hcq
          obtain ⟨ u, hu ⟩ := hcq
          rw [← hu.right]
          apply Nat.le_mul_of_pos_right
          exact Nat.pos_of_mem_divisors (hsa.right hu.left)
    exact Ne.symm (Nat.ne_of_lt this)

  -- The disjoint union will have the desired property.
  use saq.disjUnion sb disj

  constructor
  . rw [Finset.sum_disjUnion]
    rw [← hsb.left]
    simp [saq, f_emb]
    have : ∑ x ∈ sa, f x = ∑ x ∈ sa, q * x := by exact f_inj (f_inj (f_inj (f_inj rfl)))
    rw [this]
    have : ∑ x ∈ sa, q * x  = q * ∑ x ∈ sa, x := by rw [Finset.mul_sum]
    rw [this]
    rw [← hsa.left]
    linarith
  . simp
    rw [Finset.union_subset_iff]
    constructor
    . intro r hr
      simp [saq, f_emb, f] at hr
      obtain ⟨ u, hu ⟩ := hr
      rw [← hu.right]
      rw [Nat.mem_divisors]
      constructor
      . rw [mul_comm]
        rw [propext (Nat.mul_dvd_mul_iff_right hqPos)]
        obtain hsar := hsa.right hu.left
        exact Nat.dvd_of_mem_divisors hsar
      . nlinarith

    . intro r hr
      obtain hsbr := hsb.right hr
      rw [Nat.mem_divisors]
      simp at hsbr
      constructor
      . exact Dvd.dvd.mul_left (hsbr.left) p
      . nlinarith