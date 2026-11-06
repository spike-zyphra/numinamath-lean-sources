import Mathlib

/- Show that if \( a, b, \) and \( c \) are integers with \( b > 0 \) and \( c > 0 \), such that when \( a \) is divided by \( b \), the quotient is \( q \) and the remainder is \( r \), and when \( q \) is divided by \( c \), the quotient is \( t \) and the remainder is \( s \), then when \( a \) is divided by \( b c \), the quotient is \( t \) and the remainder is \( b s + r \).-/
theorem number_theory_4791 {a b c q r t s: ℤ} (hb : 0 < b) (hc : 0 < c)
    (hq : q = a / b) (hr : r = a % b) (ht : t = q / c) (hs : s = q % c) :
    a / (b * c) = t ∧ a % (b*c) = b * s + r := by
  /- 原答案错误，以下为重写的正确证明。 -/
  /- 带余除法定理具的唯一性。 -/
  rw [Int.ediv_emod_unique <| mul_pos hb hc]
  /- 带余除法定理: a=qb+r -/
  have hab := Int.ediv_add_emod a b
  rw [← hq, ← hr] at hab
  /- 带余除法定理: q=tc+s -/
  have hqc := Int.ediv_add_emod q c
  rw [← ht, ← hs] at hqc
  split_ands
  . /- 代入可得: a=bct+(bs+r) -/
    rw [← hqc] at hab
    rw [← hab]
    ring
  . /- 由b,s,r非负易得bs+r非负 -/
    have : 0 ≤ s := hs ▸ Int.emod_nonneg _ hc.ne'
    have : 0 ≤ r := hr ▸ Int.emod_nonneg _ hb.ne'
    positivity
  /- 由`s<c`和`r<b`易得`bs+r<bc` -/
  have : s < c := hs ▸ Int.emod_lt_of_pos _ hc
  have : r < b := hr ▸ Int.emod_lt_of_pos _ hb
  nlinarith
