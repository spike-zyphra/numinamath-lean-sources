import Mathlib
open Finset Nat Filter Real
set_option linter.unusedVariables false
noncomputable section

-- Define the set of numbers n satisfying the problem conditions.
def solutions (D k_q k_r : ℕ) : Finset ℕ :=
  Finset.image (fun p : ℕ × ℕ => p.1 * 10^(D-1) + p.2)
    (Finset.filter (fun p : ℕ × ℕ =>
      let d₁ := p.1; let x := p.2
      10^(D-1) ≤ d₁ * 10^(D-1) + x ∧ d₁ * 10^(D-1) + x ≤ 10^D - 1 ∧
      d₁ * 10^(D-1) + x = k_q * x + k_r ∧ k_r < x)
      (Finset.Icc 1 9 ×ˢ Finset.Icc (10^(D-2)) (10^(D-1) - 1)))

/-Let $D \ge 2$ be an integer. Let $k_q > 1$ and $k_r \ge 0$ be integers.
A positive integer $n$ has $D$ digits. Its first digit is $d_1$. Let $x$ be the $(D-1)$-digit number obtained by crossing out $d_1$. (This means $d_1 \in \{1, \dots, 9\}$, $n = d_1 \cdot 10^{D-1} + x$, and $x \in \{10^{D-2}, \dots, 10^{D-1}-1\}$ if $D > 2$, or $x \in \{0, \dots, 9\}$ if $D=2$. More generally, $0 \le x < 10^{D-1}$.)
When $n$ is divided by $x$, the quotient is $k_q$ and the remainder is $k_r$.
Find all possible values of $n$.
Show that the set of all such $n$ is $\{d_1 \cdot 10^{D-1} + x_0 \mid d_1 \in \{1, \dots, 9\} \text{ where } x_0 = \frac{d_1 \cdot 10^{D-1}-k_r}{k_q-1}, \text{ such that } (d_1 \cdot 10^{D-1}-k_r) \text{ is divisible by } (k_q-1), \text{ and } 10^{D-2} \le x_0 \le 10^{D-1}-1 \text{ (if } D \ge 2 \text{, with } 10^{-1} \text{ interpreted as } 0 \text{ for } D=2 \text{ meaning } 0 \le x_0 \le 9 \text{ ), and } k_r < x_0 \}.$
(Note: For $D=2$, $x$ is a 1-digit number, so $0 \le x \le 9$. The condition $10^{D-2} \le x_0$ should be $0 \le x_0$ if $D=2$. If $D>2$, then $x$ must be a $(D-1)$-digit number, so $10^{D-2} \le x$. We also impose $d_1 \ne 0$.)
To be precise for $x$: $x$ is a $(D-1)$-digit number means $10^{D-2} \le x \le 10^{D-1}-1$. This definition applies for $D \ge 2$.
Then the condition $10^{D-2} \le x_0 \le 10^{D-1}-1$ is appropriate for all $D \ge 2$.-/
theorem number_theory_641720 (D k_q k_r : ℕ) (hD : D ≥ 2) (hk_q : k_q > 1) :
    solutions D k_q k_r =
    Finset.image (fun p : ℕ × ℕ => p.1 * 10^(D-1) + p.2)
      (Finset.filter (fun p : ℕ × ℕ =>
        let d₁ := p.1; let x₀ := p.2
        x₀ = (d₁ * 10^(D-1) - k_r) / (k_q - 1) ∧
        (d₁ * 10^(D-1) - k_r) % (k_q - 1) = 0 ∧
        10^(D-1) ≤ d₁ * 10^(D-1) + x₀ ∧
        d₁ * 10^(D-1) + x₀ ≤ 10^D - 1 ∧
        k_r < x₀)
        (Finset.Icc 1 9 ×ˢ Finset.Icc (10^(D-2)) (10^(D-1) - 1))) := by
  ext n
  unfold solutions
  rw [Finset.mem_image, Finset.mem_image]
  -- Expand the filter condition for the solutions set.
  have h_filter_left :
    (∃ a : ℕ × ℕ, a ∈ Finset.filter
                     (fun p => 10^(D-1) ≤ p.1 * 10^(D-1) + p.2 ∧
                               p.1 * 10^(D-1) + p.2 ≤ 10^D - 1 ∧
                               p.1 * 10^(D-1) + p.2 = k_q * p.2 + k_r ∧ k_r < p.2)
                     (Icc 1 9 ×ˢ Icc (10^(D-2)) (10^(D-1) - 1)) ∧
                   a.1 * 10^(D-1) + a.2 = n) ↔
    (∃ a : ℕ × ℕ, (a ∈ Icc 1 9 ×ˢ Icc (10^(D-2)) (10^(D-1) - 1) ∧
                   10^(D-1) ≤ a.1 * 10^(D-1) + a.2 ∧
                   a.1 * 10^(D-1) + a.2 ≤ 10^D - 1 ∧
                   a.1 * 10^(D-1) + a.2 = k_q * a.2 + k_r ∧ k_r < a.2) ∧
                   a.1 * 10^(D-1) + a.2 = n) := by
    apply exists_congr
    intro a
    rw [mem_filter]
  rw [h_filter_left]
  have h_filter_right :
    (∃ a : ℕ × ℕ, a ∈ Finset.filter
                     (fun p => p.2 = (p.1 * 10^(D-1) - k_r) / (k_q - 1) ∧
                               (p.1 * 10^(D-1) - k_r) % (k_q - 1) = 0 ∧
                               10^(D-1) ≤ p.1 * 10^(D-1) + p.2 ∧
                               p.1 * 10^(D-1) + p.2 ≤ 10^D - 1 ∧ k_r < p.2)
                     (Icc 1 9 ×ˢ Icc (10^(D-2)) (10^(D-1) - 1)) ∧
                   a.1 * 10^(D-1) + a.2 = n) ↔
    (∃ a : ℕ × ℕ, (a ∈ Icc 1 9 ×ˢ Icc (10^(D-2)) (10^(D-1) - 1) ∧
                   a.2 = (a.1 * 10^(D-1) - k_r) / (k_q - 1) ∧
                   (a.1 * 10^(D-1) - k_r) % (k_q - 1) = 0 ∧
                   10^(D-1) ≤ a.1 * 10^(D-1) + a.2 ∧
                   a.1 * 10^(D-1) + a.2 ≤ 10^D - 1 ∧ k_r < a.2) ∧
                   a.1 * 10^(D-1) + a.2 = n) := by
    apply exists_congr
    intro a
    rw [mem_filter]
  rw [h_filter_right]
  -- Decompose the product set for the solutions set
  have h_product_left :
    (∃ a : ℕ × ℕ, (a ∈ Icc 1 9 ×ˢ Icc (10^(D-2)) (10^(D-1) - 1) ∧
                   10^(D-1) ≤ a.1 * 10^(D-1) + a.2 ∧
                   a.1 * 10^(D-1) + a.2 ≤ 10^D - 1 ∧
                   a.1 * 10^(D-1) + a.2 = k_q * a.2 + k_r ∧ k_r < a.2) ∧
                   a.1 * 10^(D-1) + a.2 = n) ↔
    (∃ a : ℕ × ℕ, ((a.1 ∈ Icc 1 9 ∧ a.2 ∈ Icc (10^(D-2)) (10^(D-1) - 1)) ∧
                   10^(D-1) ≤ a.1 * 10^(D-1) + a.2 ∧
                   a.1 * 10^(D-1) + a.2 ≤ 10^D - 1 ∧
                   a.1 * 10^(D-1) + a.2 = k_q * a.2 + k_r ∧ k_r < a.2) ∧
                   a.1 * 10^(D-1) + a.2 = n) := by
    apply exists_congr
    intro a
    rw [mem_product]
  rw [h_product_left]
  have h_product_right :
    (∃ a : ℕ × ℕ, (a ∈ Icc 1 9 ×ˢ Icc (10^(D-2)) (10^(D-1) - 1) ∧
                   a.2 = (a.1 * 10^(D-1) - k_r) / (k_q - 1) ∧
                   (a.1 * 10^(D-1) - k_r) % (k_q - 1) = 0 ∧
                   10^(D-1) ≤ a.1 * 10^(D-1) + a.2 ∧
                   a.1 * 10^(D-1) + a.2 ≤ 10^D - 1 ∧ k_r < a.2) ∧
                   a.1 * 10^(D-1) + a.2 = n) ↔
    (∃ a : ℕ × ℕ, ((a.1 ∈ Icc 1 9 ∧ a.2 ∈ Icc (10^(D-2)) (10^(D-1) - 1)) ∧
                   a.2 = (a.1 * 10^(D-1) - k_r) / (k_q - 1) ∧
                   (a.1 * 10^(D-1) - k_r) % (k_q - 1) = 0 ∧
                   10^(D-1) ≤ a.1 * 10^(D-1) + a.2 ∧
                   a.1 * 10^(D-1) + a.2 ≤ 10^D - 1 ∧ k_r < a.2) ∧
                   a.1 * 10^(D-1) + a.2 = n) := by
    apply exists_congr
    intro a
    rw [mem_product]
  rw [h_product_right]
  -- Expand interval membership for the solutions set.
  have h_Icc_left :
    (∃ a : ℕ × ℕ, ((a.1 ∈ Icc 1 9 ∧ a.2 ∈ Icc (10^(D-2)) (10^(D-1) - 1)) ∧
                   10^(D-1) ≤ a.1 * 10^(D-1) + a.2 ∧
                   a.1 * 10^(D-1) + a.2 ≤ 10^D - 1 ∧
                   a.1 * 10^(D-1) + a.2 = k_q * a.2 + k_r ∧ k_r < a.2) ∧
                   a.1 * 10^(D-1) + a.2 = n) ↔
    (∃ a : ℕ × ℕ, ((1 ≤ a.1 ∧ a.1 ≤ 9 ∧ 10^(D-2) ≤ a.2 ∧ a.2 ≤ 10^(D-1) - 1) ∧
                   10^(D-1) ≤ a.1 * 10^(D-1) + a.2 ∧
                   a.1 * 10^(D-1) + a.2 ≤ 10^D - 1 ∧
                   a.1 * 10^(D-1) + a.2 = k_q * a.2 + k_r ∧ k_r < a.2) ∧
                   a.1 * 10^(D-1) + a.2 = n) := by
    apply exists_congr
    intro a
    rw [mem_Icc, mem_Icc]
    simp [and_assoc]
  rw [h_Icc_left]
  -- 子目标 6：mem_Icc（右侧）
  have h_Icc_right :
    (∃ a : ℕ × ℕ, ((a.1 ∈ Icc 1 9 ∧ a.2 ∈ Icc (10^(D-2)) (10^(D-1) - 1)) ∧
                   a.2 = (a.1 * 10^(D-1) - k_r) / (k_q - 1) ∧
                   (a.1 * 10^(D-1) - k_r) % (k_q - 1) = 0 ∧
                   10^(D-1) ≤ a.1 * 10^(D-1) + a.2 ∧
                   a.1 * 10^(D-1) + a.2 ≤ 10^D - 1 ∧ k_r < a.2) ∧
                   a.1 * 10^(D-1) + a.2 = n) ↔
    (∃ a : ℕ × ℕ, ((1 ≤ a.1 ∧ a.1 ≤ 9 ∧ 10^(D-2) ≤ a.2 ∧ a.2 ≤ 10^(D-1) - 1) ∧
                   a.2 = (a.1 * 10^(D-1) - k_r) / (k_q - 1) ∧
                   (a.1 * 10^(D-1) - k_r) % (k_q - 1) = 0 ∧
                   10^(D-1) ≤ a.1 * 10^(D-1) + a.2 ∧
                   a.1 * 10^(D-1) + a.2 ≤ 10^D - 1 ∧ k_r < a.2) ∧
                   a.1 * 10^(D-1) + a.2 = n) := by
    apply exists_congr
    intro a
    rw [mem_Icc, mem_Icc]
    simp [and_assoc]
  rw [h_Icc_right]
  constructor
  -- Prove: If $n$ is in solutions, then $n$ is in the target set.
  · rintro ⟨⟨d₁, x⟩, h_a, h_n_eq⟩
    obtain ⟨⟨hd₁_min, hd₁_max, hx_min, hx_max⟩, hn_min, hn_max, h_div, hk_r_lt_x⟩ := h_a
    -- Restate the division condition.
    have h_div': d₁ * 10^(D-1) + x = k_q * x + k_r := h_div
    -- Derive the equation for $x$.
    have h_mul: d₁ * 10^(D-1) - k_r = (k_q - 1) * x := by
      rw [Nat.sub_mul]
      omega
    have h_x_eq : x = (d₁ * 10^(D-1) - k_r) / (k_q - 1) := by
      have hk_q_minus_1 : k_q - 1 ≥ 1 := by omega
      exact (Nat.div_eq_of_eq_mul_right hk_q_minus_1 h_mul).symm
    -- Prove divisibility condition.
    have h_divisible : (d₁ * 10^(D-1) - k_r) % (k_q - 1) = 0 := by
      have : (k_q - 1) ∣ (d₁ * 10^(D-1) - k_r) := by use x
      exact Nat.mod_eq_zero_of_dvd this
    -- Construct the proof for the target set.
    refine ⟨⟨d₁, x⟩, ⟨⟨hd₁_min, hd₁_max, hx_min, hx_max⟩, h_x_eq, h_divisible, hn_min, hn_max, hk_r_lt_x⟩, h_n_eq⟩
  -- Prove: If $n$ is in the target set, then $n$ is in solutions.
  · rintro ⟨⟨d₁, x₀⟩, h_a, h_n_eq⟩
    obtain ⟨⟨hd₁_min, hd₁_max, hx₀_min, hx₀_max⟩, h_x₀, h_divisible, hn_min, hn_max, hk_r_lt_x₀⟩ := h_a
    -- Derive the division condition for solutions.
    have h_div' : d₁ * 10^(D-1) + x₀ = k_q * x₀ + k_r := by
      have hk_q_minus_1 : k_q - 1 ≥ 1 := by omega
      have : (k_q - 1) * x₀ = d₁ * 10^(D-1) - k_r := by
        exact (Nat.eq_mul_of_div_eq_right (Nat.dvd_of_mod_eq_zero h_divisible) h_x₀.symm).symm
      have h_k_r_nonneg: d₁ * 10^(D-1) ≥ k_r := by
        have h_x₀_pos : x₀ > 0 := by
          cases x₀
          · have : k_r < 0 := hk_r_lt_x₀
            exact absurd this (Nat.not_lt_zero k_r)
          · exact Nat.succ_pos _
        have : (k_q - 1) * x₀ > 0 := Nat.mul_pos (by nlinarith) h_x₀_pos
        omega
      calc
        d₁ * 10^(D-1) + x₀
          = (d₁ * 10^(D-1) - k_r) + k_r + x₀ := by
            rw [Nat.sub_add_cancel h_k_r_nonneg]
        _ = (k_q - 1) * x₀ + k_r + x₀ := by rw [this]
        _ = k_q * x₀ + k_r := by
          rw [add_assoc,add_comm k_r,← add_assoc]
          have : (k_q - 1) * x₀ + x₀ + k_r = (k_q - 1) * x₀ + 1 * x₀ + k_r := by simp only [one_mul]
          rw [this,← Nat.add_mul]
          have : k_q - 1 + 1 = k_q := by omega
          rw [this]
    have h_mul : d₁ * 10^(D-1) - k_r = (k_q - 1) * x₀ := by
      rw [Nat.sub_mul]
      omega
    have h_x₀_eq : x₀ = (d₁ * 10^(D-1) - k_r) / (k_q - 1) := by
      have hk_q_minus_1 : k_q - 1 ≥ 1 := by omega
      exact (Nat.div_eq_of_eq_mul_right hk_q_minus_1 h_mul).symm
    -- Reconfirm divisibility condition.
    have h_divisible' : (d₁ * 10^(D-1) - k_r) % (k_q - 1) = 0 := by
      have : (k_q - 1) ∣ (d₁ * 10^(D-1) - k_r) := by use x₀
      exact Nat.mod_eq_zero_of_dvd this
    -- Construct the proof for the solutions set.
    refine ⟨⟨d₁, x₀⟩, ⟨⟨hd₁_min, hd₁_max, hx₀_min, hx₀_max⟩, hn_min, hn_max, h_div', hk_r_lt_x₀⟩, h_n_eq⟩
