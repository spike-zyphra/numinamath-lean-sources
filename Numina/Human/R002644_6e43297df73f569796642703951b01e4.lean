import Mathlib

open Real Finset

/-A finite set $S$ of distinct real numbers has the following properties: the mean of $S\cup\ {1\ }$ is 13 less than the mean of $S$, and the mean of $S\cup\ {2001\ }$ is 27 more than the mean of S. Find the mean of S.-/

theorem algebra_97551 {n : ℕ} (hn : 0<n) (S S1 S2: Finset ℝ)
(hS : S.card = n) (h1:S1=insert (1:Real) S)(h2:S2=insert 2001 S) (hS1 :(∑ x ∈ S, x)/S.card- (∑ x ∈ S1, x)/S1.card  = 13 ) (hS2 : (∑ x ∈ S2, x)/S2.card- (∑ x ∈ S, x)/S.card  = 27 ) : (∑ x ∈ S, x)/S.card = 651 := by
--We set mean as the mean of S. We have the following equations:
    set mean:=(∑ x ∈ S, x)/n with hmean
    have h:∑ x ∈ S, x = mean * n:=by
      rw[hmean]
      rw[←@Nat.cast_pos Real] at hn
      field_simp
--Because the mean of \( S \cup \{1\} \) is 13 less than the mean of \( S \), and the mean of \( S \cup \{2001\} \) is 27 more than the mean of \( S \), we have \( 1 \notin S \) and \( 2001 \notin S \).
    have notin: 1 ∉ S ∧ 2001 ∉ S := by
      constructor
      contrapose! hS1
      have : S1 = S := by
        rw[h1]
        simp only [insert_eq_self]
        exact hS1
      rw[this]
      simp only [sub_self, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true]
      contrapose! hS2
      have : S2 = S := by
        rw[h2]
        simp only [insert_eq_self]
        exact hS2
      rw[this]
      simp only [sub_self, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true]
    rw[h1] at hS1
    rw[h2] at hS2
--The cardinality of $S$ is $n$, so the cardinality of $S\cup\ {1\ }$ is $n+1$, and the cardinality of $S\cup\ {2001\ }$ is $n+1$.
    rw[Finset.card_insert_of_not_mem notin.1,sum_insert notin.1] at hS1
    rw[Finset.card_insert_of_not_mem notin.2,sum_insert notin.2] at hS2
    norm_num at hS1 hS2
--Substitue the definition of mean into the equations. We get linear equations about mean and n.
    rw[hS,←hmean,h] at hS1 hS2
    field_simp at hS1 hS2
    rw[hS,←hmean]
--Solve the equations, we get $mean = 651$.
    linarith only [hS1,hS2]