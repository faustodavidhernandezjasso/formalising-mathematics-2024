/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet5 -- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  rw [tendsTo_def] at *
  intros ε hε
  specialize h (ε / 37) (by linarith)
  cases' h with x hx
  use x
  intros n hn
  rw [← mul_sub_left_distrib]
  rw [abs_mul]
  rw [← one_mul ε]
  have h : (37 : ℝ) > 0
  linarith
  rw [← div_self h.ne']
  rw [abs_of_pos]
  rw [mul_comm (37/37) ε]
  rw [mul_div ε 37 37]
  rw [mul_comm ε 37]
  specialize hx n hn
  linarith
  exact h
  done

example (a b c: ℝ) (hc: c > 0) : a > b ↔ a*c > b*c := by exact Iff.symm (mul_lt_mul_right hc)
example (c b: ℝ) : c > 0 ∧ b > 0 ↔ c*b > 0 := by apply?
example (c b: ℝ) (hc: c > 0) (hb : b > 0) : c * (b / c) = c * b / c := by exact mul_div c b c
example (c b: ℝ) (hc : 0 < c) (hb : 0 < b) : c * (1 / b) = c*1/b := by exact mul_div c 1 b

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [tendsTo_def] at *
  intros ε hε
  rw [← one_div_pos] at hc
  have hεc : (0 < ε / c)
  rw [← one_mul ε]
  rw [mul_comm 1 ε]
  rw [← mul_div ε 1 c]
  apply mul_pos hε hc
  specialize h (ε / c) (by linarith)
  cases' h with x hx
  use x
  intro n hn
  rw [← mul_sub_left_distrib]
  rw [abs_mul]
  rw [← one_mul ε]
  rw [one_div_pos] at hc
  rw [← div_self hc.ne']
  rw [abs_of_pos]
  rw [mul_comm (c/c) ε]
  rw [mul_div ε c c]
  rw [mul_comm ε c]
  specialize hx n hn
  rw [← mul_lt_mul_left hc] at hx
  rw [mul_div c ε c] at hx
  exact hx
  exact hc
  done
  -- by_cases hnc: c = 0
  -- rw [hnc]
  -- simp
  -- use 0
  -- intros n hn
  -- exact hε
  -- have he : ¬c = 0 ↔ c ≠ 0
  -- simp
  -- rw [he] at hnc
  -- rw [@ne_iff_lt_or_gt] at hnc
  -- cases' hnc with hp hn
  -- specialize h (ε / c) (by linarith)
  -- cases' h with x hx
  -- use x
  -- intros n hn
  -- rw [← mul_sub_left_distrib]
  -- rw [abs_mul]
  -- rw [← one_mul ε]
  -- rw [← div_self hc.ne']
  -- rw [abs_of_pos]
  -- rw [mul_comm (c/c) ε]
  -- rw [mul_div ε c c]
  -- rw [mul_comm ε c]
  -- specialize hx n hn
  -- linarith
  -- exact hc


  -- specialize h (ε / c) (by linarith)
  -- cases' h with x hx
  -- use x
  -- intros n hn
  -- rw [← mul_sub_left_distrib]
  -- rw [abs_mul]
  -- rw [← one_mul ε]
  -- have h : (37 : ℝ) > 0
  -- linarith
  -- rw [← div_self h.ne']
  -- rw [abs_of_pos]
  -- rw [mul_comm (37/37) ε]
  -- rw [mul_div ε 37 37]
  -- rw [mul_comm ε 37]
  -- specialize hx n hn
  -- linarith
  -- exact h
  -- done

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  sorry

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  sorry

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
sorry

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
  sorry

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  sorry

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  sorry

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
sorry

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  sorry

end Section2sheet6
