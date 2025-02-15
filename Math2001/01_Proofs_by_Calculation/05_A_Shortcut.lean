/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic


import Library.Basic
--  addarith is coming from this custom library here

math2001_init


/-! # Section 1.5: A shortcut -/

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  addarith [h1]

example {a b : ℤ} (ha : a - 2 * b = 1) : a = 2 * b + 1 := by
  addarith [ha]

example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 :=
  calc
    x + y ^ 2 = x - 7 := by addarith [hy]
    _ = -5 := by addarith [hx]

-- TODO how to do this without `addarith`?
example {s t : ℝ} (h : t = 4 - s * t) : t + s * t > 0 :=
  -- have h' : t  + s * t = 4 := by
  calc
    -- t + s * t = (s + 1) * t := by ring
    -- _ = (s + 1) * ( 4 - s * t) := by rw [h] -- by addarith [h]
    t + s * t = 4 - s * t + s * t := by addarith [h]
    _ = 4 := by ring
    _ > 0 := by numbers

example {s t : ℝ} (h : t = 4 - s * t) : t + s * t > 0 := by addarith [h]

example {m n : ℝ} (h1 : m ≤ 8 - n) : 10 > m + n := by addarith [h1]


-- Check that `addarith` can't verify this deduction!
/-- error: addarith failed to prove this -/
#guard_msgs in
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
  addarith [h1] -- fails
