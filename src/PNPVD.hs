-- Andrey O. Matveev
-- Calculations for Theorem 6.4 of the monograph A.O. Matveev, Symmetric Cycles,
-- Jenny Stanford Publishing, 2023, https://www.jennystanford.com/ .
--
-- Given odd integers l', l'', l, such that 1 <= l', l'', l <= t, and positive integers j' and j'',
-- consider the following family of ordered pairs (A,B)  of disjoint unordered subsets A and B of
-- the ground set [t] :={1, 2, ..., t}:
-- { (A,B) <- 2^[t] X 2^[t]: |A\cap B| = 0,  0 < |A| = j',  0 < |B| = j'',  j'+j'' < t,
--    q(A) = l',  q(B) = l'',  q(A\dot\cup B) = l } .                                           (*)

module PNPVD
  ( theorem6Dot4I
  , theorem6Dot4II
  , theorem6Dot4III
  , theorem6Dot4IV
  , theorem6Dot4V
  ) where

import           Math.Combinatorics.Exact.Binomial (choose)

theorem6Dot4I ::
     Integer -> (Integer, Integer) -> (Integer, Integer, Integer) -> Integer
-- Theorem 6.4(i): In the family (*) there are theorem6Dot4I t (j', j'') (l', l'', l) pairs (A,B)
-- of sets A and B such that |{1,t} \cap A| = |{1,t} \cap B|=0 .
-- Call for instance (as in Example 6.5(i) of the monograph)
--      ghci> theorem6Dot4I 5 (2, 1) (3, 3, 3)
-- to get the result:
--      2
-- Call
--      ghci> theorem6Dot4I 300 (100, 150) (25, 55, 75)
-- to get the result:
--      28607408099015776367141096669404758486621255963227388737164062720
theorem6Dot4I t (j', j'') (l', l'', l)
  | t < 3 = -1 -- "N/A: t should be > 2"
  | j' <= 0 || j' > t - 2 = -2 -- "N/A: j' should be between 1 (included) and (t-2) (included)"
  | j'' <= 0 || j'' > t - 2 = -3 -- "N/A: j'' should be between 1 (included) and (t-2) (included)"
  | j' + j'' >= t = -4 -- "N/A: (j' + j'') should be < t"
  | l' < 1 || even l' = -5 -- "N/A: l' should be positive and odd"
  | l'' < 1 || even l'' = -6 -- "N/A: l'' should be positive and odd"
  | l < 1 || even l = -7 -- "N/A: l should be positive and odd"
  | otherwise =
    choose (t - (j' + j'') - 1) ((l - 1) `div` 2) *
    choose (j' - 1) ((l' - 3) `div` 2) *
    choose (j'' - 1) ((l'' - 3) `div` 2) *
    if odd ((l + l' + l'' - 1) `div` 2)
      then choose ((l - 1) `div` 2) ((l + l' - l'' - 1) `div` 4) *
           choose ((l + l' + l'' - 7) `div` 4) ((l - 3) `div` 2)
      else ((l + l' - l'' + 1) `div` 2) *
           choose ((l - 1) `div` 2) ((l + l' - l'' + 1) `div` 4) *
           choose ((l + l' + l'' - 9) `div` 4) ((l - 3) `div` 2)

theorem6Dot4II ::
     Integer -> (Integer, Integer) -> (Integer, Integer, Integer) -> Integer
-- Theorem 6.4(ii): In the family (*) there are theorem6Dot4II t (j', j'') (l', l'', l) pairs (A,B)
-- of sets A and B such that {1,t} \cap A = {1,t}, and |{1,t} \cap B| = 0.
-- Call for instance (as in Example 6.5(ii) of the monograph)
--      ghci> theorem6Dot4II 5 (2, 2) (3, 5, 3)
-- to get the result:
--      1
-- Call
--      ghci> theorem6Dot4II 300 (100, 150) (25, 55, 75)
-- to get the result:
--      193650147131799101562185885146739903601743886520308477605418270720
theorem6Dot4II t (j', j'') (l', l'', l)
  | t < 3 = -1 -- "N/A: t should be > 2"
  | j' <= 0 || j' > t - 2 = -2 -- "N/A: j' should be between 1 (included) and (t-2) (included)"
  | j'' <= 0 || j'' > t - 2 = -3 -- "N/A: j'' should be between 1 (included) and (t-2) (included)"
  | j' + j'' >= t = -4 -- "N/A: (j' + j'') should be < t"
  | l' < 1 || even l' = -5 -- "N/A: l' should be positive and odd"
  | l'' < 1 || even l'' = -6 -- "N/A: l'' should be positive and odd"
  | l < 1 || even l = -7 -- "N/A: l should be positive and odd"
  | otherwise =
    choose (t - (j' + j'') - 1) ((l - 3) `div` 2) *
    choose (j' - 1) ((l' - 1) `div` 2) *
    choose (j'' - 1) ((l'' - 3) `div` 2) *
    if odd ((l + l' + l'' - 1) `div` 2)
      then choose ((l' - 1) `div` 2) ((l + l' - l'' - 1) `div` 4) *
           choose ((l + l' + l'' - 7) `div` 4) ((l' - 3) `div` 2)
      else ((l + l' - l'' + 1) `div` 2) *
           choose ((l' - 1) `div` 2) ((l + l' - l'' + 1) `div` 4) *
           choose ((l + l' + l'' - 9) `div` 4) ((l' - 3) `div` 2)

theorem6Dot4III ::
     Integer -> (Integer, Integer) -> (Integer, Integer, Integer) -> Integer
-- Theorem 6.4(iii): In the family (*) there are theorem6Dot4III t (j', j'') (l', l'', l) pairs (A,B)
-- of sets A and B such that |{1,t} \cap A| = 0, and {1,t} \cap B = {t}.
-- Call for instance (as in Example 6.5(iii) of the monograph)
--      ghci> theorem6Dot4III 5 (1, 3) (3, 3, 1)
-- to get the result:
--      2
-- Call
--      ghci> theorem6Dot4III 300 (100, 150) (25, 55, 75)
-- to get the result:
--      211334005776512942532033326746954071702967836845463592472743526400
theorem6Dot4III t (j', j'') (l', l'', l)
  | t < 3 = -1 -- "N/A: t should be > 2"
  | j' <= 0 || j' > t - 2 = -2 -- "N/A: j' should be between 1 (included) and (t-2) (included)"
  | j'' <= 0 || j'' > t - 2 = -3 -- "N/A: j'' should be between 1 (included) and (t-2) (included)"
  | j' + j'' >= t = -4 -- "N/A: (j' + j'') should be < t"
  | l' < 1 || even l' = -5 -- "N/A: l' should be positive and odd"
  | l'' < 1 || even l'' = -6 -- "N/A: l'' should be positive and odd"
  | l < 1 || even l = -7 -- "N/A: l should be positive and odd"
  | otherwise =
    choose (t - (j' + j'') - 1) ((l - 1) `div` 2) *
    choose (j' - 1) ((l' - 3) `div` 2) *
    choose (j'' - 1) ((l'' - 1) `div` 2) *
    if odd ((l + l' + l'' + 1) `div` 2)
      then ((l + l'' - l' + 3) `div` 2) *
           choose ((l - 1) `div` 2) ((l + l'' - l' + 1) `div` 4) *
           choose ((l + l' + l'' - 5) `div` 4) ((l - 1) `div` 2)
      else choose ((l - 1) `div` 2) ((l + l'' - l' - 1) `div` 4) *
           choose ((l + l' + l'' - 3) `div` 4) ((l - 1) `div` 2) +
           ((l + l'' - l' + 3) `div` 2) *
           choose ((l - 1) `div` 2) ((l + l'' - l' + 3) `div` 4) *
           choose ((l + l' + l'' - 7) `div` 4) ((l - 1) `div` 2)

theorem6Dot4IV ::
     Integer -> (Integer, Integer) -> (Integer, Integer, Integer) -> Integer
-- Theorem 6.4(iv): In the family (*) there are theorem6Dot4IV t (j', j'') (l', l'', l) pairs (A,B)
-- of sets A and B such that {1,t} \cap A = {1}, and |{1,t} \cap B| = 0.
-- Call for instance (as in Example 6.5(iv) of the monograph)
--      ghci> theorem6Dot4IV 5 (2, 1) (3, 3, 3)
-- to get the result:
--      3
-- Call
--      ghci> theorem6Dot4IV 300 (100, 150) (25, 55, 75)
-- to get the result:
--      510294306631092227089543886535328124355946727992704772068331929600
theorem6Dot4IV t (j', j'') (l', l'', l)
  | t < 3 = -1 -- "N/A: t should be > 2"
  | j' <= 0 || j' > t - 2 = -2 -- "N/A: j' should be between 1 (included) and (t-2) (included)"
  | j'' <= 0 || j'' > t - 2 = -3 -- "N/A: j'' should be between 1 (included) and (t-2) (included)"
  | j' + j'' >= t = -4 -- "N/A: (j' + j'') should be < t"
  | l' < 1 || even l' = -5 -- "N/A: l' should be positive and odd"
  | l'' < 1 || even l'' = -6 -- "N/A: l'' should be positive and odd"
  | l < 1 || even l = -7 -- "N/A: l should be positive and odd"
  | otherwise =
    choose (t - (j' + j'') - 1) ((l - 1) `div` 2) *
    choose (j' - 1) ((l' - 1) `div` 2) *
    choose (j'' - 1) ((l'' - 3) `div` 2) *
    if odd ((l + l' + l'' + 1) `div` 2)
      then ((l + l' - l'' + 3) `div` 2) *
           choose ((l' - 1) `div` 2) ((l + l' - l'' + 1) `div` 4) *
           choose ((l + l' + l'' - 5) `div` 4) ((l' - 1) `div` 2)
      else choose ((l' - 1) `div` 2) ((l + l' - l'' - 1) `div` 4) *
           choose ((l + l' + l'' - 3) `div` 4) ((l' - 1) `div` 2) +
           ((l + l' - l'' + 3) `div` 2) *
           choose ((l' - 1) `div` 2) ((l + l' - l'' + 3) `div` 4) *
           choose ((l + l' + l'' - 7) `div` 4) ((l' - 1) `div` 2)

theorem6Dot4V ::
     Integer -> (Integer, Integer) -> (Integer, Integer, Integer) -> Integer
-- Theorem 6.4(v): In the family (*) there are theorem6Dot4V t (j', j'') (l', l'', l) pairs (A,B)
-- of sets A and B such that {1,t} \cap A = {1}, and {1,t} \cap B = {t}.
-- Call for instance (as in Example 6.5(v) of the monograph)
--      ghci> theorem6Dot4V 5 (2, 2) (3, 3, 3)
-- to get the result:
--      3
-- Call
--      ghci> theorem6Dot4V 300 (100, 150) (25, 55, 75)
-- to get the result:
--      44844353516354588241391379514073749898885320387712176156588064358400
theorem6Dot4V t (j', j'') (l', l'', l)
  | t < 3 = -1 -- "N/A: t should be > 2"
  | j' <= 0 || j' > t - 2 = -2 -- "N/A: j' should be between 1 (included) and (t-2) (included)"
  | j'' <= 0 || j'' > t - 2 = -3 -- "N/A: j'' should be between 1 (included) and (t-2) (included)"
  | j' + j'' >= t = -4 -- "N/A: (j' + j'') should be < t"
  | l' < 1 || even l' = -5 -- "N/A: l' should be positive and odd"
  | l'' < 1 || even l'' = -6 -- "N/A: l'' should be positive and odd"
  | l < 1 || even l = -7 -- "N/A: l should be positive and odd"
  | otherwise =
    choose (t - (j' + j'') - 1) ((l - 3) `div` 2) *
    choose (j' - 1) ((l' - 1) `div` 2) *
    choose (j'' - 1) ((l'' - 1) `div` 2) *
    if odd ((l + l' + l'' + 1) `div` 2)
      then ((l' + l'' - l + 3) `div` 2) *
           choose ((l' - 1) `div` 2) ((l' + l'' - l + 1) `div` 4) *
           choose ((l + l' + l'' - 5) `div` 4) ((l' - 1) `div` 2)
      else choose ((l' - 1) `div` 2) ((l' + l'' - l - 1) `div` 4) *
           choose ((l + l' + l'' - 3) `div` 4) ((l' - 1) `div` 2) +
           ((l' + l'' - l + 3) `div` 2) *
           choose ((l' - 1) `div` 2) ((l' + l'' - l + 3) `div` 4) *
           choose ((l + l' + l'' - 7) `div` 4) ((l' - 1) `div` 2)
