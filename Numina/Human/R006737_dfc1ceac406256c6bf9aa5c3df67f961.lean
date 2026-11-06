import Mathlib


/-Let $n$ and $m$ be positive natural numbers such that $m < n$. Let $s_0$ be a natural number.
A square table of size $n \times n$ is constructed such that for $0 \le r < n$ and $0 \le c < n$,
the cell at row $r$ and column $c$ (0-indexed) contains the number $s_0 + r \cdot n + c$.
From this table, an $m \times m$ square subgrid is cut out, with its top-left corner
at row $r_0$ and column $c_0$ (where $0 \le r_0 \le n-m$ and $0 \le c_0 \le n-m$).
Let $S$ be the sum of the numbers in this $m \times m$ subgrid.
Prove that $2S$ is divisible by $m^2$.-/

open BigOperators Nat Finset
set_option linter.unusedVariables false

theorem number_theory_640658 (n m s0 r0 c0 S : ℕ) (hn : n > 0) (hm : m > 0) (hmn : m < n)
    (hr0 : r0 ≤ n - m) (hc0 : c0 ≤ n - m)
    (hS : S = s0 * m ^ 2 + (n * r0 + c0) * m ^ 2  + ∑ i ∈ Finset.range m, (∑ j ∈ Finset.range m, (j * n + i))) :
    2 * S % (m ^ 2) = 0 := by
  -- The sum S can be expressed as a double sum over the indices of the subgrid

  -- prove ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j * n) = n * ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j)
  have sum_1 : ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j * n) = n * ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j) := by
    calc ∑ _ ∈ range m, (∑ j ∈ range m, j * n)
        = ∑ _ ∈ range m, (∑ j ∈ range m, j) * n := by simp [show ∑ j ∈ range m, j * n = (∑ j ∈ range m, j) * n by exact Eq.symm (sum_mul (range m) (fun i => i) n) ]
      _ = (∑ _ ∈ range m, (∑ j ∈ range m, j)) * n := by exact Eq.symm (sum_mul (range m) (fun i => ∑ j ∈ range m, j) n)
      _ = n * ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j) := by group

  -- prove ∑ i ∈ Finset.range m, (∑ _ ∈ Finset.range m, i) = ∑ j ∈ Finset.range m, (∑ _ ∈ Finset.range m, j)
  have sum_sum_i : ∑ i ∈ Finset.range m, (∑ _ ∈ Finset.range m, i) = ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j) := by
    exact sum_comm

  -- prove ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j) = m ^ 2 * (m - 1) / 2
  have sum_2 : ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j) = m * (m * (m - 1) / 2) := by
    calc
          ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j)
      _ = ∑ _ ∈ Finset.range m, (m * (m - 1) / 2) := by simp [show (∑ j ∈ Finset.range m, j) = m * (m - 1) / 2 by exact sum_range_id m]
      _ = m * (m * (m - 1) / 2) := by field_simp

  -- prove 2 * (n + 1) * (m * (m * (m - 1) / 2) = (n + 1) * m ^ 2 * (m - 1)
  have h_relation_convert : 2 * (n + 1) * (m * (m * (m - 1) / 2)) = (n + 1) * m ^ 2 * (m - 1) := by
    have : Even (m * (m - 1)) := by exact even_mul_pred_self m
    calc  2 * (n + 1) * (m * (m * (m - 1) / 2))
      _ = (n + 1) * m * (2 * (m * (m - 1) / 2)) := by group
      _ = (n + 1) * m * (m * (m - 1)) := by simp [show (2 * (m * (m - 1) / 2)) = m * (m - 1) by exact two_mul_div_two_of_even this]
      _ = (n + 1) * m ^ 2 * (m - 1) := by group


  -- prove ∑ i ∈ Finset.range m, (∑ j ∈ Finset.range m, (j * n + i)) = m ^ 2 * (m - 1) / 2 * (n + 1)
  have sum_3 : ∑ i ∈ Finset.range m, (∑ j ∈ Finset.range m, (j * n + i)) = (n + 1) * (m * (m * (m - 1) / 2)) := by
    calc
          ∑ i ∈ Finset.range m, (∑ j ∈ Finset.range m, (j * n + i))
      _ = ∑ i ∈ Finset.range m, ((∑ j ∈ Finset.range m, j * n) + ∑ _ ∈ Finset.range m, i) := by simp only [Finset.sum_add_distrib]
      _ = ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j * n) + ∑ i ∈ Finset.range m, (∑ _ ∈ Finset.range m, i) := by exact sum_add_distrib

      _ = n * ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j) + ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j) := by rw [sum_1, sum_sum_i]
      _ = (n + 1) * ∑ _ ∈ Finset.range m, (∑ j ∈ Finset.range m, j) := by group

      _ = (n + 1) * (m * (m * (m - 1) / 2)) := by simp [sum_2]

  -- prove (2 * s0 * m ^ 2 + 2 * (n * r0 + c0) * m ^ 2) % m ^ 2
  have hS_mod1 : (2 * s0 * m ^ 2 + 2 * (n * r0 + c0) * m ^ 2) % m ^ 2 = 0 := by
    field_simp

  calc
    2 * S % m ^ 2
    _ = 2 * (s0 * m ^ 2 + (n * r0 + c0) * m ^ 2  + (n + 1) * (m * (m * (m - 1) / 2))) % m ^ 2 := by simp [hS, sum_3]

    _ = (2 * s0 * m ^ 2 + 2 * (n * r0 + c0) * m ^ 2  + 2 * (n + 1) * (m * (m * (m - 1) / 2))) % m ^ 2 := by group
    _ = ((2 * s0 * m ^ 2 + 2 * (n * r0 + c0) * m ^ 2) % m ^ 2 + 2 * (n + 1) * (m * (m * (m - 1) / 2)) % m ^ 2) % m ^ 2 := by exact add_mod (2 * s0 * m ^ 2 + 2 * (n * r0 + c0) * m ^ 2) (2 * (n + 1) * (m * (m * (m - 1) / 2))) (m ^ 2)
    _ = (0 + 2 * (n + 1) * (m * (m * (m - 1) / 2)) % m ^ 2) % m ^ 2 := by simp [hS_mod1]

    _ = (0 + (n + 1) * m ^ 2 * (m - 1)) % m ^ 2 % m ^ 2 := by simp [h_relation_convert]
    _ = (n + 1) * (m - 1) * m ^ 2 % m ^ 2 % m ^ 2 := by group
    _ = 0 := by field_simp