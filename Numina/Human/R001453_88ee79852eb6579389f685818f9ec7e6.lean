import Mathlib

open scoped Pointwise

/-Let $\mathbb{Z}$ and $\mathbb{Q}$ be the sets of integers and rationals respectively.  a) Does there exist a partition of $\mathbb{Z}$ into three non-empty subsets $A, B, C$ such that the sets $A+B, B+C, C+A$ are disjoint?  b) Does there exist a partition of $\mathbb{Q}$ into three non-empty subsets $A, B, C$ such that the sets $A+B, B+C, C+A$ are disjoint?  Here $X+Y$ denotes the set $\{x+y \mid x \in X, y \in Y\}$, for $X, Y \subseteq \mathbb{Z}$ and $X, Y \subseteq \mathbb{Q}$.-/
theorem A2_b (A B C : Set ℚ)
(neA : Nonempty A) (neB : Nonempty B) (neC : Nonempty C)
(dAB : A ∩ B = ∅) (dBC : B ∩ C = ∅) (dCA : C ∩ A = ∅)
(uABC : A ∪ B ∪ C = Set.univ)
(d1 : (A + B) ∩ (B + C) = ∅) (d2 : (B + C) ∩ (C + A) = ∅) (d3 : (C + A) ∩ (A + B) = ∅) : False := by
-- The answer to the second part is no, suppose we have such sets $A$, $B$ and $C$
-- As nonempty sets, we can pick one elements from each of the sets $A$, $B$ and $C$
  rcases neA with ⟨a, ha⟩
  rcases neB with ⟨b, hb⟩
  rcases neC with ⟨c, hc⟩
-- Prove three symmetric lemmas about the sets $A$, $B$ and $C$
  have AaBsC : ∀ x y z, x ∈ A → y ∈ B → z ∈ C → x + y - z ∈ C := by
-- introduce variables and assumptions, we will prove by contradiction
    intro x y z hx hy hz; by_contra h'
-- Rewrite assumptions so that we can see $x+y-z$ has to be in $A$ or in $B$
    rw [← Set.mem_compl_iff, Set.compl_eq_univ_diff] at h'
    rw [← uABC, Set.union_diff_cancel_right] at h'
-- Split the goal to the cases when $x+y-z$ is in $A$ or in $B$
    simp at h'; cases h'; rename_i h'
-- Show that in the first case, $x+y$ lies in both $C+A$ and $A+B$,
-- which is a contradiction since we required these sets to be disjoint.
    · have : x + y ∈ (C + A) ∩ (A + B) := by
        simp; constructor
        · simp [Set.mem_add]; use z
          constructor; assumption; use x+y-z
          constructor; assumption; ring
        simp [Set.mem_add]; use x
        constructor; assumption; use y
      rw [d3] at this; contradiction
-- Show that in the second case, $x+y$ lies in both $A+B$ and $B+C$,
-- which is a contradiction since we required these sets to be disjoint.
    rename_i h'
    · have : x + y ∈ (A + B) ∩ (B + C) := by
        simp; constructor
        · simp [Set.mem_add]; use x
          constructor; assumption; use y
        simp [Set.mem_add]; use x+y-z
        constructor; assumption; use z
        constructor; assumption; ring
      rw [d1] at this; contradiction
-- Prove one last disjointness properties which is required by the lemma Set.union_diff_cancel_right
    rw [Set.union_inter_distrib_right, dBC, Set.inter_comm, dCA]; simp

  have AsBaC : ∀ x y z, x ∈ A → y ∈ B → z ∈ C → x - y + z ∈ B := by
-- introduce variables and assumptions, we will prove by contradiction
    intro x y z hx hy hz; by_contra h'
-- Rewrite assumptions so that we can see $x-y+z$ has to be in $C$ or in $A$
    rw [← Set.mem_compl_iff, Set.compl_eq_univ_diff] at h'
    rw [← uABC, Set.union_comm, ← Set.union_assoc, Set.union_diff_cancel_right] at h'
-- Split the goal to the cases when $x-y+z$ is in $C$ or in $A$
    simp at h'; cases h'; rename_i h'
-- Show that in the first case, $x+z$ lies in both $B+C$ and $C+A$,
-- which is a contradiction since we required these sets to be disjoint.
    · have : x + z ∈ (B + C) ∩ (C + A) := by
        simp; constructor
        · simp [Set.mem_add]; use y
          constructor; assumption; use x-y+z
          constructor; assumption; ring
        simp [Set.mem_add]; use z
        constructor; assumption; use x
        constructor; assumption; ring
      rw [d2] at this; contradiction
-- Show that in the second case, $x+z$ lies in both $C+A$ and $A+B$,
-- which is a contradiction since we required these sets to be disjoint.
    rename_i h'
    · have : x + z ∈ (C + A) ∩ (A + B) := by
        simp; constructor
        · simp [Set.mem_add]; use z
          constructor; assumption; use x
          constructor; assumption; ring
        simp [Set.mem_add]; use x-y+z
        constructor; assumption; use y
        constructor; assumption; ring
      rw [d3] at this; contradiction
-- Prove one last disjointness properties which is required by the lemma Set.union_diff_cancel_right
    rw [Set.union_inter_distrib_right, dAB, Set.inter_comm, dBC]; simp

  have BaCsA : ∀ x y z, x ∈ A → y ∈ B → z ∈ C → - x + y + z ∈ A := by
-- introduce variables and assumptions, we will prove by contradiction
    intro x y z hx hy hz; by_contra h'
-- Rewrite assumptions so that we can see $-x+y+z$ has to be in $B$ or in $C$
    rw [← Set.mem_compl_iff, Set.compl_eq_univ_diff] at h'
    rw [← uABC, Set.union_assoc, Set.union_diff_cancel_left] at h'
-- Split  the goal to the cases when $-x+y+z$ is in $B$ or in $C$
    simp at h'; cases h'; rename_i h'
-- Show that in the first case, $y+z$ lies in both $A+B$ and $B+C$,
-- which is a contradiction since we required these sets to be disjoint.
    · have : y + z ∈ (A + B) ∩ (B + C) := by
        simp; constructor
        · simp [Set.mem_add]; use x
          constructor; assumption; use -x+y+z
          constructor; assumption; ring
        simp [Set.mem_add]; use y
        constructor; assumption; use z
      rw [d1] at this; contradiction
-- Show that in the first case, $y+z$ lies in both $B+C$ and $C+A$,
-- which is a contradiction since we required these sets to be disjoint.
    rename_i h'
    · have : y + z ∈ (B + C) ∩ (C + A) := by
        simp; constructor
        · simp [Set.mem_add]; use y
          constructor; assumption; use z
        simp [Set.mem_add]; use -x+y+z
        constructor; assumption; use x
        constructor; assumption; ring
      rw [d2] at this; contradiction
-- Prove one last disjointness properties which is required by the lemma Set.union_diff_cancel_left
    rw [Set.inter_union_distrib_left, dAB, Set.inter_comm, dCA]; simp

-- Split to three symmetric cases when $0$ is in $A$, in $B$ or in $C$
  have : (0 : ℚ) ∈ Set.univ := by simp
  rw [← uABC] at this; simp at this; cases this
  rename_i h'; cases h'; rename_i h'
-- In the first case, we prove that $A$ has to be the whole set $ℚ$ in two steps
  · have AeQ : A = Set.univ := by
-- The first step is to prove that $A+A+A$ is the whole set $ℚ$
      have A3eQ : A + A + A = Set.univ := by
        ext x; simp; simp [Set.ext_iff] at uABC
-- Split the goal to three cases when $x/3$ is in $A$, in $B$ or in $C$
        cases uABC (x/3); rename_i h
        cases h; rename_i h
-- When $x/3$ is in $A$, rewriting $x$ as $x/3+x/3+x/3$ will finish the goal
        · simp [Set.mem_add]; use x/3; constructor; assumption
          use x/3; constructor; assumption
          use x/3; constructor; assumption; ring
        rename_i h
-- When $x/3$ is in $B$, rewriting $x$ as $(x/3+x/3-c)+(x/3+c)+0$ will finish the goal
        · simp [Set.mem_add]; use -0+x/3+(0+x/3-c); constructor
          apply BaCsA; any_goals assumption
          apply AaBsC; any_goals assumption
          use -0+x/3+c; constructor
          apply BaCsA; assumption; assumption; assumption
          use 0; constructor; assumption; ring
-- When $x/3$ is in $C$, rewriting $x$ as $(-b+x/3+x/3)+(b+x/3)+0$ will finish the goal
        rename_i h; simp [Set.mem_add]; use -0+(0-b+x/3)+x/3; constructor
        apply BaCsA; assumption
        apply AsBaC; any_goals assumption
        use -0+b+x/3; constructor
        apply BaCsA; any_goals assumption
        use 0; constructor; assumption; ring
-- The second step is to prove that $A$ equals $A+A+A$
      have A3eA : A = A + A + A := by
        ext x; constructor
-- For any $x$ in $A$, rewriting $x$ as $x+0+0$ proves $x$ is in $A+A+A$
        · intro hx; simp [Set.mem_add]; use x
          constructor; assumption; use 0
          constructor; assumption; use 0
          constructor; assumption; ring
        simp [Set.mem_add]; intro a1 ha1 a2 ha2 a3 ha3 h
-- Conversely, for any $a1+a2+a3$ in $A+A+A$, rewriting it as
-- $-0+((-0+(a1-b+c)+(a2+b-c))-b+c)+(a3+b-c)$ and apply lemma BaCsA proves it is in $A$
        rw [show a1+a2+a3=-0+((-0+(a1-b+c)+(a2+b-c))-b+c)+(a3+b-c) by ring] at h
        rw [← h]; apply BaCsA; assumption
        apply AsBaC; apply BaCsA; assumption
        apply AsBaC; any_goals assumption
        apply AaBsC; any_goals assumption
        apply AaBsC; any_goals assumption
      rw [A3eA]; assumption
-- Now we have proved that $A$ is the whole set $ℚ$
-- this will force $B$ to be empty, which is a contradiction
    simp [AeQ] at dAB; rw [dAB] at hb; contradiction

-- In the second case, we prove that $B$ has to be the whole set $ℚ$ in two steps
  rename_i h'
  · have BeQ : B = Set.univ := by
-- The first step is to prove that $B+B+B$ is the whole set $ℚ$
      have B3eQ : B + B + B = Set.univ := by
        ext x; simp; simp [Set.ext_iff] at uABC
-- Split the goal to three cases when $x/3$ is in $A$, in $B$ or in $C$
        cases uABC (x/3); rename_i h
        cases h; rename_i h
-- When $x/3$ is in $A$, rewriting $x$ as $(x/3+x/3-c)+(x/3+c)+0$ will finish the goal
        · simp [Set.mem_add]; use x/3-0+(x/3+0-c); constructor
          apply AsBaC; any_goals assumption
          apply AaBsC; any_goals assumption
          use x/3-0+c; constructor
          apply AsBaC; any_goals assumption
          use 0; constructor; assumption; ring
        rename_i h
-- When $x/3$ is in $B$, rewriting $x$ as $x/3+x/3+x/3$ will finish the goal
        · simp [Set.mem_add]; use x/3; constructor; assumption
          use x/3; constructor; assumption
          use x/3; constructor; assumption; ring
-- When $x/3$ is in $A$, rewriting $x$ as $(-a+x/3+x/3)+(a+x/3)+0$ will finish the goal
        rename_i h; simp [Set.mem_add]; use (-a+0+x/3)-0+x/3; constructor
        apply AsBaC; apply BaCsA; any_goals assumption
        use a-0+x/3; constructor
        apply AsBaC; any_goals assumption
        use 0; constructor; assumption; ring
-- The second step is to prove that $B$ equals $B+B+B$
      have B3eB : B = B + B + B := by
        ext x; constructor
-- For any $x$ in $B$, rewriting $x$ as $x+0+0$ proves $x$ is in $B+B+B$
        · intro hx; simp [Set.mem_add]; use x
          constructor; assumption; use 0
          constructor; assumption; use 0
          constructor; assumption; ring
-- Conversely, for any $b1+b2+b3$ in $B+B+B$, rewriting it as
-- $(-a+b1+c)-0+(a+((-a+b2+c)-0+(a+b3-c))-c)$ and apply lemma AsBaC proves it is in $B$
        simp [Set.mem_add]; intro b1 hb1 b2 hb2 b3 hb3 h
        rw [show b1+b2+b3=(-a+b1+c)-0+(a+((-a+b2+c)-0+(a+b3-c))-c) by ring] at h
        rw [← h]; apply AsBaC; apply BaCsA; any_goals assumption
        apply AaBsC; assumption; apply AsBaC; apply BaCsA
        any_goals assumption
        apply AaBsC; any_goals assumption
      rw [B3eB]; assumption
-- Now we have proved that $B$ is the whole set $ℚ$
-- this will force $A$ to be empty, which is a contradiction
    simp [BeQ] at dAB; rw [dAB] at ha; contradiction

-- In the last case, we prove that $C$ has to be the whole set $ℚ$ in two steps
  rename_i h'
  have CeQ : C = Set.univ := by
-- The first step is to prove that $C+C+C$ is the whole set $ℚ$
    have C3eQ : C + C + C = Set.univ := by
      ext x; simp; simp [Set.ext_iff] at uABC
      cases uABC (x/3); rename_i h
      cases h; rename_i h
-- When $x/3$ is in $A$, rewriting $x$ as $(x/3+x/3-b)+(x/3+b)+0$ will finish the goal
      · simp [Set.mem_add]; use x/3+(x/3-b+0)-0; constructor
        apply AaBsC; assumption
        apply AsBaC; any_goals assumption
        use x/3+b-0; constructor
        apply AaBsC; any_goals assumption
        use 0; constructor; assumption; ring
-- When $x/3$ is in $B$, rewriting $x$ as $(-a+x/3+x/3)+(a+x/3)+c$ will finish the goal
      rename_i h
      · simp [Set.mem_add]; use (-a+x/3+0)+x/3-0; constructor
        apply AaBsC; apply BaCsA; any_goals assumption
        use a+x/3-0; constructor
        apply AaBsC; any_goals assumption
        use 0; constructor; assumption; ring
-- When $x/3$ is in $C$, rewriting $x$ as $x/3+x/3+x/3$ will finish the goal
      rename_i h; simp [Set.mem_add]; use x/3; constructor; assumption
      use x/3; constructor; assumption
      use x/3; constructor; assumption; ring
-- The second step is to prove that $C$ equals $C+C+C$
    have C3eC : C = C + C + C := by
      ext x; constructor
-- For any $x$ in $C$, rewriting $x$ as $x+0+0$ proves $x$ is in $C+C+C$
      · intro hx; simp [Set.mem_add]; use x
        constructor; assumption; use 0
        constructor; assumption; use 0
        constructor; assumption; ring
-- Conversely, for any $c1+c2+c3$ in $C+C+C$, rewriting it as
-- $(-a+b+((-a+b+c1)+(a-b+c2)-0))+(a-b+c3)-0$ and apply lemma AaBsC proves it is in $C$
      simp [Set.mem_add]; intro c1 hc1 c2 hc2 c3 hc3 h
      rw [show c1+c2+c3=(-a+b+((-a+b+c1)+(a-b+c2)-0))+(a-b+c3)-0 by ring] at h
      rw [← h]; apply AaBsC; apply BaCsA; any_goals assumption
      apply AaBsC; apply BaCsA
      any_goals assumption
      apply AsBaC; any_goals assumption
      apply AsBaC; any_goals assumption
    rw [C3eC]; assumption
-- Now we have proved that $C$ is the whole set $ℚ$
-- this will force $B$ to be empty, which is a contradiction
  simp [CeQ] at dBC; rw [dBC] at hb; contradiction

/-Let $\mathbb{Z}$ and $\mathbb{Q}$ be the sets of integers and rationals respectively.  a) Does there exist a partition of $\mathbb{Z}$ into three non-empty subsets $A, B, C$ such that the sets $A+B, B+C, C+A$ are disjoint?  b) Does there exist a partition of $\mathbb{Q}$ into three non-empty subsets $A, B, C$ such that the sets $A+B, B+C, C+A$ are disjoint?  Here $X+Y$ denotes the set $\{x+y \mid x \in X, y \in Y\}$, for $X, Y \subseteq \mathbb{Z}$ and $X, Y \subseteq \mathbb{Q}$.-/
theorem A2_a : ∃ A B C : Set ℤ, Nonempty A ∧ Nonempty B ∧
Nonempty C ∧ A ∪ B ∪ C = Set.univ ∧ A ∩ B = ∅ ∧ B ∩ C = ∅ ∧
C ∩ A = ∅ ∧ (A + B) ∩ (B + C) = ∅ ∧ (B + C) ∩ (C + A) = ∅ ∧
(C + A) ∩ (A + B) = ∅ := by
-- The answer to the first part is yes.
-- We prove that the three residue classes modulo $3$ is such a partition
  let A := {x : ℤ | x % 3 = 0}
  let B := {x : ℤ | x % 3 = 1}
  let C := {x : ℤ | x % 3 = 2}
-- Prove the three residue classes are nonempty by exhibiting one element in each set
-- we use $0$ for $A$, $1$ for $B$ and $2$ for $C$
  use A; use B; use C; constructor; use 0; simp [A]
  constructor; use 1; simp [B]
  constructor; use 2; simp [C]
  constructor
-- Prove the union of the thress residue classes is the whole set $ℤ$,
-- we use division with remainders in $ℤ$ and prove the remainder is less than $3$
  · ext x; simp [A, B, C]
    have xm3 := Int.emod_add_ediv x 3
    have m3le := Int.emod_lt_of_pos x (show (0:ℤ)<3 by norm_num)
    have m3ge := Int.emod_nonneg x (show (3:ℤ)≠0 by norm_num)
    by_cases h : 3 ∣ x;
    · left; left; assumption
    rw [Int.dvd_iff_emod_eq_zero] at h; push_neg at h
-- Use "interval_cases (x % 3)" to handle the three cases efficiently
    interval_cases (x % 3); contradiction; simp; simp

-- Prove that the three residue classes are pairwisely disjoint,
-- this is because each residue class has a different remainder modulo $3$
  constructor
  · simp [A, B]; ext x; simp
    intro h; rw [Int.dvd_iff_emod_eq_zero] at h
    rw [h]; simp
  constructor
  · simp [B, C]; ext x; simp
    intro h; rw [h]; simp
  constructor
  · simp [C, A]; ext x; simp
    intro h; rw [Int.dvd_iff_emod_eq_zero, h]; simp

-- Prove the required disjointness properties on $A+B$, $B+C$ and $C+A$
-- we explicitly write out the assumptions and apply division with remainder in each case,
-- then compare their remainders modulo $3$.
  constructor
-- The remainders modulo $3$ for numbers in $A+B$, $B+C$ are $1$ and $0$ respectively,
-- therefore they must be disjoint
  · ext x; simp [A,B,C, Set.mem_add]
    intro y hy z hz hyz w hw u hu hwu
    rw [Int.dvd_iff_emod_eq_zero] at hy
    rw [← Int.emod_add_ediv y 3, ← Int.emod_add_ediv z 3] at hyz
    rw [hy, hz] at hyz; ring_nf at hyz
    rw [add_assoc, ← Int.add_mul] at hyz
    apply_fun (fun x => x % 3) at hyz
    rw [Int.add_mul_emod_self] at hyz; simp at hyz

    rw [← Int.emod_add_ediv w 3, ← Int.emod_add_ediv u 3] at hwu
    rw [hw, hu] at hwu; ring_nf at hwu
    rw [add_assoc, ← Int.add_mul] at hwu
    apply_fun (fun x => x % 3) at hwu
    rw [Int.add_mul_emod_self] at hwu; simp at hwu; linarith
  constructor
-- The remainders modulo $3$ for numbers in $B+C$, $C+A$ are $0$ and $2$ respectively,
-- therefore they must be disjoint
  · ext x; simp [A,B,C, Set.mem_add]
    intro y hy z hz hyz w hw u hu hwu
    rw [Int.dvd_iff_emod_eq_zero] at hu
    rw [← Int.emod_add_ediv y 3, ← Int.emod_add_ediv z 3] at hyz
    rw [hy, hz] at hyz; ring_nf at hyz
    rw [add_assoc, ← Int.add_mul] at hyz
    apply_fun (fun x => x % 3) at hyz
    rw [Int.add_mul_emod_self] at hyz; simp at hyz

    rw [← Int.emod_add_ediv w 3, ← Int.emod_add_ediv u 3] at hwu
    rw [hw, hu] at hwu; ring_nf at hwu
    rw [add_assoc, ← Int.add_mul] at hwu
    apply_fun (fun x => x % 3) at hwu
    rw [Int.add_mul_emod_self] at hwu; simp at hwu; linarith
-- The remainders modulo $3$ for numbers in $C+A$, $A+B$ are $2$ and $1$ respectively,
-- therefore they must be disjoint
  ext x; simp [A,B,C, Set.mem_add]
  intro y hy z hz hyz w hw u hu hwu
  rw [Int.dvd_iff_emod_eq_zero] at hz hw
  rw [← Int.emod_add_ediv y 3, ← Int.emod_add_ediv z 3] at hyz
  rw [hy, hz] at hyz; ring_nf at hyz
  rw [add_assoc, ← Int.add_mul] at hyz
  apply_fun (fun x => x % 3) at hyz
  rw [Int.add_mul_emod_self] at hyz; simp at hyz

  rw [← Int.emod_add_ediv w 3, ← Int.emod_add_ediv u 3] at hwu
  rw [hw, hu] at hwu; ring_nf at hwu
  rw [add_assoc, ← Int.add_mul] at hwu
  apply_fun (fun x => x % 3) at hwu
  rw [Int.add_mul_emod_self] at hwu; simp at hwu; linarith