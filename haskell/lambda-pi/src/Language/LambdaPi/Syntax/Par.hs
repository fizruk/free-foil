{-# OPTIONS_GHC -w #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.LambdaPi.Syntax.Par
  ( happyError
  , myLexer
  , pProgram
  , pCommand
  , pListCommand
  , pTerm2
  , pTerm
  , pTerm1
  , pScopedTerm
  , pPattern
  ) where

import Prelude

import qualified Language.LambdaPi.Syntax.Abs
import Language.LambdaPi.Syntax.Lex
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.1.1

data HappyAbsSyn 
	= HappyTerminal (Token)
	| HappyErrorToken Prelude.Int
	| HappyAbsSyn11 (Language.LambdaPi.Syntax.Abs.VarIdent)
	| HappyAbsSyn12 (Language.LambdaPi.Syntax.Abs.Program)
	| HappyAbsSyn13 (Language.LambdaPi.Syntax.Abs.Command)
	| HappyAbsSyn14 ([Language.LambdaPi.Syntax.Abs.Command])
	| HappyAbsSyn15 (Language.LambdaPi.Syntax.Abs.Term)
	| HappyAbsSyn18 (Language.LambdaPi.Syntax.Abs.ScopedTerm)
	| HappyAbsSyn19 (Language.LambdaPi.Syntax.Abs.Pattern)

{- to allow type-synonyms as our monads (likely
 - with explicitly-specified bind and return)
 - in Haskell98, it seems that with
 - /type M a = .../, then /(HappyReduction M)/
 - is not allowed.  But Happy is a
 - code-generator that can just substitute it.
type HappyReduction m = 
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> m HappyAbsSyn
-}

action_0,
 action_1,
 action_2,
 action_3,
 action_4,
 action_5,
 action_6,
 action_7,
 action_8,
 action_9,
 action_10,
 action_11,
 action_12,
 action_13,
 action_14,
 action_15,
 action_16,
 action_17,
 action_18,
 action_19,
 action_20,
 action_21,
 action_22,
 action_23,
 action_24,
 action_25,
 action_26,
 action_27,
 action_28,
 action_29,
 action_30,
 action_31,
 action_32,
 action_33,
 action_34,
 action_35,
 action_36,
 action_37,
 action_38,
 action_39,
 action_40,
 action_41,
 action_42,
 action_43,
 action_44,
 action_45,
 action_46,
 action_47,
 action_48,
 action_49,
 action_50,
 action_51,
 action_52,
 action_53,
 action_54,
 action_55,
 action_56,
 action_57,
 action_58,
 action_59,
 action_60,
 action_61,
 action_62,
 action_63,
 action_64,
 action_65,
 action_66,
 action_67,
 action_68,
 action_69,
 action_70,
 action_71,
 action_72 :: () => Prelude.Int -> ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyReduce_8,
 happyReduce_9,
 happyReduce_10,
 happyReduce_11,
 happyReduce_12,
 happyReduce_13,
 happyReduce_14,
 happyReduce_15,
 happyReduce_16,
 happyReduce_17,
 happyReduce_18,
 happyReduce_19,
 happyReduce_20,
 happyReduce_21,
 happyReduce_22,
 happyReduce_23,
 happyReduce_24,
 happyReduce_25,
 happyReduce_26,
 happyReduce_27,
 happyReduce_28,
 happyReduce_29 :: () => ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,149) ([0,3072,0,32768,1,0,48,0,4,4,128,222,4096,4096,0,30722,3,4160,64,0,2048,0,0,0,0,0,0,0,32768,32800,0,0,0,0,0,0,0,0,0,0,256,258,0,0,0,61444,6,128,0,4096,4100,0,2,0,64,0,0,0,0,1,1,32800,55,0,0,0,0,0,512,0,0,0,16384,28416,0,57352,13,0,0,0,0,0,0,0,2048,0,0,1,0,768,0,128,0,0,0,0,48129,1,32800,55,8192,0,32768,32800,0,96,0,512,512,0,1,0,520,8,256,256,0,0,0,61444,6,2048,0,4096,7104,0,4,0,128,0,0,0,0,48129,1,32800,55,0,0,0,0,0,0,0,0,0,0,0,0,57352,13,512,0,16384,0,0,0,0,0,0,8192,0,0,32768,0,64,111,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram","%start_pCommand","%start_pListCommand","%start_pTerm2","%start_pTerm","%start_pTerm1","%start_pScopedTerm","%start_pPattern","VarIdent","Program","Command","ListCommand","Term2","Term","Term1","ScopedTerm","Pattern","'('","')'","','","'.'","':'","';'","'_'","'check'","'compute'","'\215'","'\928'","'\955'","'\960\8321'","'\960\8322'","'\8594'","'\120140'","L_VarIdent","%eof"]
        bit_start = st Prelude.* 37
        bit_end = (st Prelude.+ 1) Prelude.* 37
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..36]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (27) = happyShift action_31
action_0 (28) = happyShift action_32
action_0 (12) = happyGoto action_34
action_0 (13) = happyGoto action_29
action_0 (14) = happyGoto action_35
action_0 _ = happyReduce_12

action_1 (27) = happyShift action_31
action_1 (28) = happyShift action_32
action_1 (13) = happyGoto action_33
action_1 _ = happyFail (happyExpListPerState 1)

action_2 (27) = happyShift action_31
action_2 (28) = happyShift action_32
action_2 (13) = happyGoto action_29
action_2 (14) = happyGoto action_30
action_2 _ = happyReduce_12

action_3 (20) = happyShift action_26
action_3 (36) = happyShift action_9
action_3 (11) = happyGoto action_14
action_3 (15) = happyGoto action_28
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (20) = happyShift action_19
action_4 (30) = happyShift action_20
action_4 (31) = happyShift action_21
action_4 (32) = happyShift action_22
action_4 (33) = happyShift action_23
action_4 (35) = happyShift action_24
action_4 (36) = happyShift action_9
action_4 (11) = happyGoto action_14
action_4 (15) = happyGoto action_15
action_4 (16) = happyGoto action_27
action_4 (17) = happyGoto action_17
action_4 _ = happyFail (happyExpListPerState 4)

action_5 (20) = happyShift action_26
action_5 (36) = happyShift action_9
action_5 (11) = happyGoto action_14
action_5 (15) = happyGoto action_15
action_5 (17) = happyGoto action_25
action_5 _ = happyFail (happyExpListPerState 5)

action_6 (20) = happyShift action_19
action_6 (30) = happyShift action_20
action_6 (31) = happyShift action_21
action_6 (32) = happyShift action_22
action_6 (33) = happyShift action_23
action_6 (35) = happyShift action_24
action_6 (36) = happyShift action_9
action_6 (11) = happyGoto action_14
action_6 (15) = happyGoto action_15
action_6 (16) = happyGoto action_16
action_6 (17) = happyGoto action_17
action_6 (18) = happyGoto action_18
action_6 _ = happyFail (happyExpListPerState 6)

action_7 (20) = happyShift action_12
action_7 (26) = happyShift action_13
action_7 (36) = happyShift action_9
action_7 (11) = happyGoto action_10
action_7 (19) = happyGoto action_11
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (36) = happyShift action_9
action_8 _ = happyFail (happyExpListPerState 8)

action_9 _ = happyReduce_8

action_10 _ = happyReduce_28

action_11 (37) = happyAccept
action_11 _ = happyFail (happyExpListPerState 11)

action_12 (20) = happyShift action_12
action_12 (26) = happyShift action_13
action_12 (36) = happyShift action_9
action_12 (11) = happyGoto action_10
action_12 (19) = happyGoto action_47
action_12 _ = happyFail (happyExpListPerState 12)

action_13 _ = happyReduce_27

action_14 _ = happyReduce_14

action_15 _ = happyReduce_25

action_16 _ = happyReduce_26

action_17 (20) = happyShift action_26
action_17 (29) = happyShift action_46
action_17 (36) = happyShift action_9
action_17 (11) = happyGoto action_14
action_17 (15) = happyGoto action_40
action_17 _ = happyReduce_23

action_18 (37) = happyAccept
action_18 _ = happyFail (happyExpListPerState 18)

action_19 (20) = happyShift action_19
action_19 (30) = happyShift action_20
action_19 (31) = happyShift action_21
action_19 (32) = happyShift action_22
action_19 (33) = happyShift action_23
action_19 (35) = happyShift action_24
action_19 (36) = happyShift action_9
action_19 (11) = happyGoto action_14
action_19 (15) = happyGoto action_15
action_19 (16) = happyGoto action_45
action_19 (17) = happyGoto action_17
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (20) = happyShift action_44
action_20 _ = happyFail (happyExpListPerState 20)

action_21 (20) = happyShift action_12
action_21 (26) = happyShift action_13
action_21 (36) = happyShift action_9
action_21 (11) = happyGoto action_10
action_21 (19) = happyGoto action_43
action_21 _ = happyFail (happyExpListPerState 21)

action_22 (20) = happyShift action_42
action_22 _ = happyFail (happyExpListPerState 22)

action_23 (20) = happyShift action_41
action_23 _ = happyFail (happyExpListPerState 23)

action_24 _ = happyReduce_22

action_25 (20) = happyShift action_26
action_25 (36) = happyShift action_9
action_25 (37) = happyAccept
action_25 (11) = happyGoto action_14
action_25 (15) = happyGoto action_40
action_25 _ = happyFail (happyExpListPerState 25)

action_26 (20) = happyShift action_19
action_26 (30) = happyShift action_20
action_26 (31) = happyShift action_21
action_26 (32) = happyShift action_22
action_26 (33) = happyShift action_23
action_26 (35) = happyShift action_24
action_26 (36) = happyShift action_9
action_26 (11) = happyGoto action_14
action_26 (15) = happyGoto action_15
action_26 (16) = happyGoto action_39
action_26 (17) = happyGoto action_17
action_26 _ = happyFail (happyExpListPerState 26)

action_27 (37) = happyAccept
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (37) = happyAccept
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (25) = happyShift action_38
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (37) = happyAccept
action_30 _ = happyFail (happyExpListPerState 30)

action_31 (20) = happyShift action_19
action_31 (30) = happyShift action_20
action_31 (31) = happyShift action_21
action_31 (32) = happyShift action_22
action_31 (33) = happyShift action_23
action_31 (35) = happyShift action_24
action_31 (36) = happyShift action_9
action_31 (11) = happyGoto action_14
action_31 (15) = happyGoto action_15
action_31 (16) = happyGoto action_37
action_31 (17) = happyGoto action_17
action_31 _ = happyFail (happyExpListPerState 31)

action_32 (20) = happyShift action_19
action_32 (30) = happyShift action_20
action_32 (31) = happyShift action_21
action_32 (32) = happyShift action_22
action_32 (33) = happyShift action_23
action_32 (35) = happyShift action_24
action_32 (36) = happyShift action_9
action_32 (11) = happyGoto action_14
action_32 (15) = happyGoto action_15
action_32 (16) = happyGoto action_36
action_32 (17) = happyGoto action_17
action_32 _ = happyFail (happyExpListPerState 32)

action_33 (37) = happyAccept
action_33 _ = happyFail (happyExpListPerState 33)

action_34 (37) = happyAccept
action_34 _ = happyFail (happyExpListPerState 34)

action_35 _ = happyReduce_9

action_36 (24) = happyShift action_58
action_36 _ = happyFail (happyExpListPerState 36)

action_37 (24) = happyShift action_57
action_37 _ = happyFail (happyExpListPerState 37)

action_38 (27) = happyShift action_31
action_38 (28) = happyShift action_32
action_38 (13) = happyGoto action_29
action_38 (14) = happyGoto action_56
action_38 _ = happyReduce_12

action_39 (21) = happyShift action_50
action_39 _ = happyFail (happyExpListPerState 39)

action_40 _ = happyReduce_24

action_41 (20) = happyShift action_19
action_41 (30) = happyShift action_20
action_41 (31) = happyShift action_21
action_41 (32) = happyShift action_22
action_41 (33) = happyShift action_23
action_41 (35) = happyShift action_24
action_41 (36) = happyShift action_9
action_41 (11) = happyGoto action_14
action_41 (15) = happyGoto action_15
action_41 (16) = happyGoto action_55
action_41 (17) = happyGoto action_17
action_41 _ = happyFail (happyExpListPerState 41)

action_42 (20) = happyShift action_19
action_42 (30) = happyShift action_20
action_42 (31) = happyShift action_21
action_42 (32) = happyShift action_22
action_42 (33) = happyShift action_23
action_42 (35) = happyShift action_24
action_42 (36) = happyShift action_9
action_42 (11) = happyGoto action_14
action_42 (15) = happyGoto action_15
action_42 (16) = happyGoto action_54
action_42 (17) = happyGoto action_17
action_42 _ = happyFail (happyExpListPerState 42)

action_43 (23) = happyShift action_53
action_43 _ = happyFail (happyExpListPerState 43)

action_44 (20) = happyShift action_12
action_44 (26) = happyShift action_13
action_44 (36) = happyShift action_9
action_44 (11) = happyGoto action_10
action_44 (19) = happyGoto action_52
action_44 _ = happyFail (happyExpListPerState 44)

action_45 (21) = happyShift action_50
action_45 (22) = happyShift action_51
action_45 _ = happyFail (happyExpListPerState 45)

action_46 (20) = happyShift action_26
action_46 (36) = happyShift action_9
action_46 (11) = happyGoto action_14
action_46 (15) = happyGoto action_15
action_46 (17) = happyGoto action_49
action_46 _ = happyFail (happyExpListPerState 46)

action_47 (22) = happyShift action_48
action_47 _ = happyFail (happyExpListPerState 47)

action_48 (20) = happyShift action_12
action_48 (26) = happyShift action_13
action_48 (36) = happyShift action_9
action_48 (11) = happyGoto action_10
action_48 (19) = happyGoto action_66
action_48 _ = happyFail (happyExpListPerState 48)

action_49 (20) = happyShift action_26
action_49 (36) = happyShift action_9
action_49 (11) = happyGoto action_14
action_49 (15) = happyGoto action_40
action_49 _ = happyReduce_18

action_50 _ = happyReduce_15

action_51 (20) = happyShift action_19
action_51 (30) = happyShift action_20
action_51 (31) = happyShift action_21
action_51 (32) = happyShift action_22
action_51 (33) = happyShift action_23
action_51 (35) = happyShift action_24
action_51 (36) = happyShift action_9
action_51 (11) = happyGoto action_14
action_51 (15) = happyGoto action_15
action_51 (16) = happyGoto action_65
action_51 (17) = happyGoto action_17
action_51 _ = happyFail (happyExpListPerState 51)

action_52 (24) = happyShift action_64
action_52 _ = happyFail (happyExpListPerState 52)

action_53 (20) = happyShift action_19
action_53 (30) = happyShift action_20
action_53 (31) = happyShift action_21
action_53 (32) = happyShift action_22
action_53 (33) = happyShift action_23
action_53 (35) = happyShift action_24
action_53 (36) = happyShift action_9
action_53 (11) = happyGoto action_14
action_53 (15) = happyGoto action_15
action_53 (16) = happyGoto action_16
action_53 (17) = happyGoto action_17
action_53 (18) = happyGoto action_63
action_53 _ = happyFail (happyExpListPerState 53)

action_54 (21) = happyShift action_62
action_54 _ = happyFail (happyExpListPerState 54)

action_55 (21) = happyShift action_61
action_55 _ = happyFail (happyExpListPerState 55)

action_56 _ = happyReduce_13

action_57 (20) = happyShift action_19
action_57 (30) = happyShift action_20
action_57 (31) = happyShift action_21
action_57 (32) = happyShift action_22
action_57 (33) = happyShift action_23
action_57 (35) = happyShift action_24
action_57 (36) = happyShift action_9
action_57 (11) = happyGoto action_14
action_57 (15) = happyGoto action_15
action_57 (16) = happyGoto action_60
action_57 (17) = happyGoto action_17
action_57 _ = happyFail (happyExpListPerState 57)

action_58 (20) = happyShift action_19
action_58 (30) = happyShift action_20
action_58 (31) = happyShift action_21
action_58 (32) = happyShift action_22
action_58 (33) = happyShift action_23
action_58 (35) = happyShift action_24
action_58 (36) = happyShift action_9
action_58 (11) = happyGoto action_14
action_58 (15) = happyGoto action_15
action_58 (16) = happyGoto action_59
action_58 (17) = happyGoto action_17
action_58 _ = happyFail (happyExpListPerState 58)

action_59 _ = happyReduce_11

action_60 _ = happyReduce_10

action_61 _ = happyReduce_21

action_62 _ = happyReduce_20

action_63 _ = happyReduce_17

action_64 (20) = happyShift action_19
action_64 (30) = happyShift action_20
action_64 (31) = happyShift action_21
action_64 (32) = happyShift action_22
action_64 (33) = happyShift action_23
action_64 (35) = happyShift action_24
action_64 (36) = happyShift action_9
action_64 (11) = happyGoto action_14
action_64 (15) = happyGoto action_15
action_64 (16) = happyGoto action_69
action_64 (17) = happyGoto action_17
action_64 _ = happyFail (happyExpListPerState 64)

action_65 (21) = happyShift action_68
action_65 _ = happyFail (happyExpListPerState 65)

action_66 (21) = happyShift action_67
action_66 _ = happyFail (happyExpListPerState 66)

action_67 _ = happyReduce_29

action_68 _ = happyReduce_19

action_69 (21) = happyShift action_70
action_69 _ = happyFail (happyExpListPerState 69)

action_70 (34) = happyShift action_71
action_70 _ = happyFail (happyExpListPerState 70)

action_71 (20) = happyShift action_19
action_71 (30) = happyShift action_20
action_71 (31) = happyShift action_21
action_71 (32) = happyShift action_22
action_71 (33) = happyShift action_23
action_71 (35) = happyShift action_24
action_71 (36) = happyShift action_9
action_71 (11) = happyGoto action_14
action_71 (15) = happyGoto action_15
action_71 (16) = happyGoto action_16
action_71 (17) = happyGoto action_17
action_71 (18) = happyGoto action_72
action_71 _ = happyFail (happyExpListPerState 71)

action_72 _ = happyReduce_16

happyReduce_8 = happySpecReduce_1  11 happyReduction_8
happyReduction_8 (HappyTerminal (PT _ (T_VarIdent happy_var_1)))
	 =  HappyAbsSyn11
		 (Language.LambdaPi.Syntax.Abs.VarIdent happy_var_1
	)
happyReduction_8 _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_1  12 happyReduction_9
happyReduction_9 (HappyAbsSyn14  happy_var_1)
	 =  HappyAbsSyn12
		 (Language.LambdaPi.Syntax.Abs.AProgram happy_var_1
	)
happyReduction_9 _  = notHappyAtAll 

happyReduce_10 = happyReduce 4 13 happyReduction_10
happyReduction_10 ((HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn13
		 (Language.LambdaPi.Syntax.Abs.CommandCheck happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_11 = happyReduce 4 13 happyReduction_11
happyReduction_11 ((HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn13
		 (Language.LambdaPi.Syntax.Abs.CommandCompute happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_12 = happySpecReduce_0  14 happyReduction_12
happyReduction_12  =  HappyAbsSyn14
		 ([]
	)

happyReduce_13 = happySpecReduce_3  14 happyReduction_13
happyReduction_13 (HappyAbsSyn14  happy_var_3)
	_
	(HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn14
		 ((:) happy_var_1 happy_var_3
	)
happyReduction_13 _ _ _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_1  15 happyReduction_14
happyReduction_14 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn15
		 (Language.LambdaPi.Syntax.Abs.Var happy_var_1
	)
happyReduction_14 _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_3  15 happyReduction_15
happyReduction_15 _
	(HappyAbsSyn15  happy_var_2)
	_
	 =  HappyAbsSyn15
		 (happy_var_2
	)
happyReduction_15 _ _ _  = notHappyAtAll 

happyReduce_16 = happyReduce 8 16 happyReduction_16
happyReduction_16 ((HappyAbsSyn18  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 (Language.LambdaPi.Syntax.Abs.Pi happy_var_3 happy_var_5 happy_var_8
	) `HappyStk` happyRest

happyReduce_17 = happyReduce 4 16 happyReduction_17
happyReduction_17 ((HappyAbsSyn18  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 (Language.LambdaPi.Syntax.Abs.Lam happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_18 = happySpecReduce_3  16 happyReduction_18
happyReduction_18 (HappyAbsSyn15  happy_var_3)
	_
	(HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 (Language.LambdaPi.Syntax.Abs.Product happy_var_1 happy_var_3
	)
happyReduction_18 _ _ _  = notHappyAtAll 

happyReduce_19 = happyReduce 5 16 happyReduction_19
happyReduction_19 (_ `HappyStk`
	(HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 (Language.LambdaPi.Syntax.Abs.Pair happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_20 = happyReduce 4 16 happyReduction_20
happyReduction_20 (_ `HappyStk`
	(HappyAbsSyn15  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 (Language.LambdaPi.Syntax.Abs.First happy_var_3
	) `HappyStk` happyRest

happyReduce_21 = happyReduce 4 16 happyReduction_21
happyReduction_21 (_ `HappyStk`
	(HappyAbsSyn15  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 (Language.LambdaPi.Syntax.Abs.Second happy_var_3
	) `HappyStk` happyRest

happyReduce_22 = happySpecReduce_1  16 happyReduction_22
happyReduction_22 _
	 =  HappyAbsSyn15
		 (Language.LambdaPi.Syntax.Abs.Universe
	)

happyReduce_23 = happySpecReduce_1  16 happyReduction_23
happyReduction_23 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 (happy_var_1
	)
happyReduction_23 _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_2  17 happyReduction_24
happyReduction_24 (HappyAbsSyn15  happy_var_2)
	(HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 (Language.LambdaPi.Syntax.Abs.App happy_var_1 happy_var_2
	)
happyReduction_24 _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_1  17 happyReduction_25
happyReduction_25 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 (happy_var_1
	)
happyReduction_25 _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_1  18 happyReduction_26
happyReduction_26 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn18
		 (Language.LambdaPi.Syntax.Abs.AScopedTerm happy_var_1
	)
happyReduction_26 _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_1  19 happyReduction_27
happyReduction_27 _
	 =  HappyAbsSyn19
		 (Language.LambdaPi.Syntax.Abs.PatternWildcard
	)

happyReduce_28 = happySpecReduce_1  19 happyReduction_28
happyReduction_28 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn19
		 (Language.LambdaPi.Syntax.Abs.PatternVar happy_var_1
	)
happyReduction_28 _  = notHappyAtAll 

happyReduce_29 = happyReduce 5 19 happyReduction_29
happyReduction_29 (_ `HappyStk`
	(HappyAbsSyn19  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Language.LambdaPi.Syntax.Abs.PatternPair happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyNewToken action sts stk [] =
	action 37 37 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 20;
	PT _ (TS _ 2) -> cont 21;
	PT _ (TS _ 3) -> cont 22;
	PT _ (TS _ 4) -> cont 23;
	PT _ (TS _ 5) -> cont 24;
	PT _ (TS _ 6) -> cont 25;
	PT _ (TS _ 7) -> cont 26;
	PT _ (TS _ 8) -> cont 27;
	PT _ (TS _ 9) -> cont 28;
	PT _ (TS _ 10) -> cont 29;
	PT _ (TS _ 11) -> cont 30;
	PT _ (TS _ 12) -> cont 31;
	PT _ (TS _ 13) -> cont 32;
	PT _ (TS _ 14) -> cont 33;
	PT _ (TS _ 15) -> cont 34;
	PT _ (TS _ 16) -> cont 35;
	PT _ (T_VarIdent happy_dollar_dollar) -> cont 36;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 37 tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = ((>>=))
happyReturn :: () => a -> Err a
happyReturn = (return)
happyThen1 m k tks = ((>>=)) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (return) a
happyError' :: () => ([(Token)], [Prelude.String]) -> Err a
happyError' = (\(tokens, _) -> happyError tokens)
pProgram tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn12 z -> happyReturn z; _other -> notHappyAtAll })

pCommand tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn13 z -> happyReturn z; _other -> notHappyAtAll })

pListCommand tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_2 tks) (\x -> case x of {HappyAbsSyn14 z -> happyReturn z; _other -> notHappyAtAll })

pTerm2 tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_3 tks) (\x -> case x of {HappyAbsSyn15 z -> happyReturn z; _other -> notHappyAtAll })

pTerm tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_4 tks) (\x -> case x of {HappyAbsSyn15 z -> happyReturn z; _other -> notHappyAtAll })

pTerm1 tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_5 tks) (\x -> case x of {HappyAbsSyn15 z -> happyReturn z; _other -> notHappyAtAll })

pScopedTerm tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_6 tks) (\x -> case x of {HappyAbsSyn18 z -> happyReturn z; _other -> notHappyAtAll })

pPattern tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_7 tks) (\x -> case x of {HappyAbsSyn19 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $










































data Happy_IntList = HappyCons Prelude.Int Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action









































indexShortOffAddr arr off = arr Happy_Data_Array.! off


{-# INLINE happyLt #-}
happyLt x y = (x Prelude.< y)






readArrayBit arr bit =
    Bits.testBit (indexShortOffAddr arr (bit `Prelude.div` 16)) (bit `Prelude.mod` 16)






-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Prelude.Int ->                    -- token number
         Prelude.Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Prelude.- ((1) :: Prelude.Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             _ = nt :: Prelude.Int
             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n Prelude.- ((1) :: Prelude.Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Prelude.- ((1)::Prelude.Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction









happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ((HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.









{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
