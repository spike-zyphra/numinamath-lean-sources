import Mathlib

/-Let
$$
S(n, r)=\binom{n-1}{r-1}+\binom{n-1}{r}+\binom{n-1}{r+1}+\cdots+\binom{n-1}{n-1}
$$
for all $n, r>0$, and in particular $S(n, r)=0$ if $r>n>0$. Prove that the number in row $n$ of the table, $r$ columns to the left of the 1 in the top row, is at most $S(n, r)$. (Hint: First prove that $S(n-1, r-1)+S(n-1, r)=S(n, r)$.)-/
theorem combinatorics_611290 {n r : ℕ} (hr : 1 < r) (hn : 1 < n) (h : r ≤ n) :
    ∑ i ∈ Finset.Ico (r - 1) n, (n - 1).choose i =
      ∑ i ∈ Finset.Ico (r - 2) (n - 1), (n - 2).choose i +
      ∑ i ∈ Finset.Ico (r - 1) (n - 1), (n - 2).choose i := by
  have h_num_pairs : n - r = Finset.card (Finset.range (n - r)) := (Finset.card_range (n - r)).symm
  -- Prove that the right-hand side equals the paired sum plus the extra term.
  have h_right : ∑ i ∈ Finset.Ico (r - 2) (n - 1), (n - 2).choose i + ∑ i ∈ Finset.Ico (r - 1) (n - 1), (n - 2).choose i =
      ∑ s ∈ Finset.range (n - r), ((n - 2).choose (r - 2 + s) + (n - 2).choose (r - 1 + s)) + (n - 2).choose (n - 2) := by
    have h_left_sum : ∑ i ∈ Finset.Ico (r - 2) (n - 1), (n - 2).choose i =
        ∑ s ∈ Finset.range (n - r + 1), (n - 2).choose (r - 2 + s) := by
      rw [Finset.sum_Ico_eq_sum_range]
      congr 1
      have : n - 1 - (r - 2) = n - r + 1 := by omega
      rw [this]
    have h_right_sum : ∑ i ∈ Finset.Ico (r - 1) (n - 1), (n - 2).choose i =
        ∑ s ∈ Finset.range (n - r), (n - 2).choose (r - 1 + s) := by
      rw [Finset.sum_Ico_eq_sum_range]
      congr 1
      have : n - 1 - (r - 1) = n - r := by omega
      rw [this]
    rw [h_left_sum, h_right_sum]
    rw [Finset.sum_range_succ]
    have h_extra_term : (n - 2).choose (r - 2 + (n - r)) = (n - 2).choose (n - 2) := by congr 1; omega
    rw [h_extra_term, Nat.add_right_comm, Finset.sum_add_distrib.symm]
  rw [h_right]
  -- Prove each paired term using Pascal's identity.
  have h_pair : ∀ s, s < n - r → (n - 2).choose (r - 2 + s) + (n - 2).choose (r - 1 + s) = (n - 1).choose (r - 1 + s) := by
    intro s hs
    have h_eq1: (r - 1 + s) = (r - 2 + s) + 1 := by omega
    have h_eq2: (n - 1) = (n - 2) + 1 := by omega
    rw [h_eq1, h_eq2, ← Nat.choose_succ_succ' (n - 2) (r - 2 + s)]
  -- Handle the extra term for the last binomial coefficient.
  have h_extra : (n - 2).choose (n - 2) = (n - 1).choose (n - 1) := by
    rw [Nat.choose_self (n - 1), Nat.choose_self (n - 2)]
  rw [Finset.sum_congr rfl fun s mem => h_pair s (Finset.mem_range.mp mem)]
  rw [h_extra]
  -- Convert the sum over range to sum over Ico interval.
  have h_sum_i : ∑ s ∈ Finset.range (n - r), (n - 1).choose (r - 1 + s) = ∑ i ∈ Finset.Ico (r - 1) (n - 1), (n - 1).choose i := by
    rw [Finset.sum_Ico_eq_sum_range]
    congr 1
    have : n - 1 - (r - 1) = n - r := by omega
    rw [this]
  rw [h_sum_i]
  -- Adjust the left-hand side by adding the last term.
  have h_left : ∑ i ∈ Finset.Ico (r - 1) n, (n - 1).choose i = ∑ i ∈ Finset.Ico (r - 1) (n - 1), (n - 1).choose i + (n - 1).choose (n - 1) := by
    have h_eq: ∑ i ∈ Finset.Ico (r - 1) n, (n - 1).choose i = ∑ i ∈ Finset.Ico (r - 1) ((n - 1) + 1), (n - 1).choose i := by
      have : ((n - 1) + 1) = n := by omega
      rw [this]
    rw [h_eq, Finset.sum_Ico_succ_top (Nat.sub_le_sub_right h 1) (fun i => (n - 1).choose i)]
  rw [h_left]
