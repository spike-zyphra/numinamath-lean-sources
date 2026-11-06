import Mathlib

/-Déterminer tous les quadruplets ( $a, b, c, d$ d'entiers positifs avec $a, b, c$ strictement positifs tels que

$$
\begin{aligned}
& \operatorname{PPCM}(b, c)=a+d \\
& \operatorname{PPCM}(c, a)=b+d \\
& \operatorname{PPCM}(a, b)=c+d
\end{aligned}
$$-/
theorem number_theory_607178 (a b c d : ℕ) (apos : 0 < a) (bpos : 0 < b) (cpos : 0 < c) :
(b.lcm c = a + d ∧ c.lcm a = b + d ∧ a.lcm b = c + d) ↔ a = b ∧ b = c ∧ d = 0 := by
-- Assume w. l. o. g. that $a$ is less or equal to $c$
  wlog alec : a ≤ c
  · specialize this c b a d cpos bpos apos (show _ by linarith)
    rw [Nat.lcm_comm]; nth_rw 2 [Nat.lcm_comm]; nth_rw 3 [Nat.lcm_comm]
    rw [and_comm]; nth_rw 2 [and_comm]; rw [and_assoc, this]
    constructor; any_goals intro; split_ands; any_goals linarith
-- Assume w. l. o. g. that $b$ is less or equal to $c$
  wlog blec : b ≤ c
  · specialize this a c b d apos cpos bpos (show _ by linarith) (show _ by linarith)
    rw [Nat.lcm_comm]; nth_rw 2 [Nat.lcm_comm]; nth_rw 3 [Nat.lcm_comm]
    nth_rw 2 [and_comm]; rw [this]
    constructor; any_goals intro; split_ands; any_goals linarith
-- Assume w. l. o. g. that $a$ is less or equal to $b$
  wlog aleb : a ≤ b
  · specialize this b a c d bpos apos cpos blec alec (show _ by linarith)
    rw [Nat.lcm_comm]; nth_rw 2 [Nat.lcm_comm]; nth_rw 3 [Nat.lcm_comm]
    rw [and_comm, and_assoc]; nth_rw 2 [and_comm]; rw [this]
    constructor; any_goals intro; split_ands; any_goals linarith
  constructor
  -- To prove the "if" part, we first show that $c$ divides $b-a$
  · rintro ⟨hbc, hca, hab⟩; have cdvd : c ∣ b - a := by
      rw [← Nat.add_sub_add_right _ d]; apply Nat.dvd_sub'
      rw [← hca]; apply Nat.dvd_lcm_left; rw [← hbc]; apply Nat.dvd_lcm_right
  -- Show that it suffices to prove $a=b$
    suffices : b = a
    · simp [this] at hab; simp [hab] at alec; simp [alec] at hab
      split_ands; any_goals linarith
  -- Assume the contrary that $b≠a$, we derive a contradiction that $b-a$ is greater or equal to $c$
    by_contra! h; apply Nat.le_of_dvd at cdvd
    rw [Nat.le_sub_iff_add_le] at cdvd; any_goals linarith
    rw [Nat.sub_pos_iff_lt, Nat.lt_iff_le_and_ne]; symm at h; constructor
    any_goals assumption
-- Conversely, it is straightforward to check that if $a=b$, $b=c$ and $d=0$, the desired identities hold
  rintro ⟨hab, hbc, hd⟩; simp [hab, hbc, hd]