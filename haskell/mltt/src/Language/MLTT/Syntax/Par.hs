{-# OPTIONS_GHC -w #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.MLTT.Syntax.Par
  ( happyError
  , myLexer
  , pProgram
  , pListCommand
  , pCommand
  , pTerm
  , pTerm1
  , pTerm2
  , pScopedTerm
  , pPattern
  ) where

import Prelude

import qualified Language.MLTT.Syntax.Abs
import Language.MLTT.Syntax.Lex
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.1.1

data HappyAbsSyn 
	= HappyTerminal (Token)
	| HappyErrorToken Prelude.Int
	| HappyAbsSyn11 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.VarIdent))
	| HappyAbsSyn12 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Program))
	| HappyAbsSyn13 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Command]))
	| HappyAbsSyn14 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Command))
	| HappyAbsSyn15 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Term))
	| HappyAbsSyn18 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.ScopedTerm))
	| HappyAbsSyn19 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Pattern))

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
 action_72,
 action_73,
 action_74,
 action_75,
 action_76,
 action_77,
 action_78,
 action_79,
 action_80,
 action_81,
 action_82,
 action_83,
 action_84,
 action_85,
 action_86,
 action_87,
 action_88,
 action_89,
 action_90,
 action_91,
 action_92,
 action_93,
 action_94,
 action_95,
 action_96,
 action_97,
 action_98,
 action_99,
 action_100,
 action_101,
 action_102,
 action_103,
 action_104,
 action_105,
 action_106,
 action_107,
 action_108,
 action_109,
 action_110,
 action_111 :: () => Prelude.Int -> ({-HappyReduction (Err) = -}
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
 happyReduce_29,
 happyReduce_30,
 happyReduce_31,
 happyReduce_32,
 happyReduce_33,
 happyReduce_34,
 happyReduce_35,
 happyReduce_36,
 happyReduce_37,
 happyReduce_38,
 happyReduce_39 :: () => ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,265) ([0,49152,1,0,49152,1,0,49152,1,0,6152,30684,0,6152,30232,0,6152,30232,0,6152,30684,0,8200,16384,0,0,16384,0,0,0,0,0,0,0,0,0,0,8200,16384,0,0,0,0,0,0,0,0,0,0,6152,32312,0,0,0,0,0,0,0,6152,30684,0,8,0,0,8,0,0,8200,16384,0,8,0,0,0,0,0,8,0,0,8,0,0,8200,16384,0,6152,30232,0,6152,30232,0,0,0,0,0,0,0,0,0,0,6152,30232,0,0,0,0,0,0,0,6152,30684,0,6152,30684,0,0,16384,0,0,0,0,512,0,0,0,0,0,0,0,0,49152,1,0,128,0,0,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,64,0,0,8200,16384,0,8200,16384,0,6152,30684,0,1024,0,0,6152,30684,0,6152,30684,0,176,0,0,6152,30684,0,6152,30684,0,32,0,0,8200,16384,0,0,0,0,0,0,0,0,0,0,6152,30684,0,6152,30684,0,32,0,0,32,0,0,6152,30684,0,16,0,0,128,0,0,128,0,0,6152,30684,0,6152,30684,0,6152,30684,0,0,0,0,256,0,0,0,0,0,0,0,0,6152,30684,0,6152,30684,0,0,0,0,0,2,0,6152,30684,0,6152,30684,0,16,0,0,16,0,0,16,0,0,0,0,0,0,0,0,0,0,0,32,0,0,32,0,0,6152,30684,0,16,0,0,16,0,0,6152,30684,0,0,0,0,0,32,0,0,2048,0,0,0,0,6152,30684,0,6152,30684,0,16,0,0,16,0,0,6152,30684,0,6152,30684,0,0,0,0,0,0,0,0,0,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram_internal","%start_pListCommand_internal","%start_pCommand_internal","%start_pTerm_internal","%start_pTerm1_internal","%start_pTerm2_internal","%start_pScopedTerm_internal","%start_pPattern_internal","VarIdent","Program","ListCommand","Command","Term","Term1","Term2","ScopedTerm","Pattern","'('","')'","','","'.'","':'","':='","';'","'='","'Id'","'J'","'_'","'check'","'compute'","'def'","'in'","'let'","'refl'","'tt'","'\215'","'\928'","'\931'","'\955'","'\960\8321'","'\960\8322'","'\8594'","'\120140'","'\120793'","L_VarIdent","%eof"]
        bit_start = st Prelude.* 48
        bit_end = (st Prelude.+ 1) Prelude.* 48
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..47]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (31) = happyShift action_36
action_0 (32) = happyShift action_37
action_0 (33) = happyShift action_38
action_0 (12) = happyGoto action_41
action_0 (13) = happyGoto action_42
action_0 (14) = happyGoto action_40
action_0 _ = happyReduce_10

action_1 (31) = happyShift action_36
action_1 (32) = happyShift action_37
action_1 (33) = happyShift action_38
action_1 (13) = happyGoto action_39
action_1 (14) = happyGoto action_40
action_1 _ = happyReduce_10

action_2 (31) = happyShift action_36
action_2 (32) = happyShift action_37
action_2 (33) = happyShift action_38
action_2 (14) = happyGoto action_35
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (20) = happyShift action_19
action_3 (28) = happyShift action_20
action_3 (29) = happyShift action_21
action_3 (35) = happyShift action_22
action_3 (36) = happyShift action_23
action_3 (37) = happyShift action_24
action_3 (39) = happyShift action_25
action_3 (40) = happyShift action_26
action_3 (41) = happyShift action_27
action_3 (42) = happyShift action_28
action_3 (43) = happyShift action_29
action_3 (45) = happyShift action_30
action_3 (46) = happyShift action_31
action_3 (47) = happyShift action_9
action_3 (11) = happyGoto action_14
action_3 (15) = happyGoto action_34
action_3 (16) = happyGoto action_16
action_3 (17) = happyGoto action_17
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (20) = happyShift action_19
action_4 (28) = happyShift action_20
action_4 (29) = happyShift action_21
action_4 (36) = happyShift action_23
action_4 (37) = happyShift action_24
action_4 (42) = happyShift action_28
action_4 (43) = happyShift action_29
action_4 (45) = happyShift action_30
action_4 (46) = happyShift action_31
action_4 (47) = happyShift action_9
action_4 (11) = happyGoto action_14
action_4 (16) = happyGoto action_33
action_4 (17) = happyGoto action_17
action_4 _ = happyFail (happyExpListPerState 4)

action_5 (20) = happyShift action_19
action_5 (28) = happyShift action_20
action_5 (29) = happyShift action_21
action_5 (36) = happyShift action_23
action_5 (37) = happyShift action_24
action_5 (42) = happyShift action_28
action_5 (43) = happyShift action_29
action_5 (45) = happyShift action_30
action_5 (46) = happyShift action_31
action_5 (47) = happyShift action_9
action_5 (11) = happyGoto action_14
action_5 (17) = happyGoto action_32
action_5 _ = happyFail (happyExpListPerState 5)

action_6 (20) = happyShift action_19
action_6 (28) = happyShift action_20
action_6 (29) = happyShift action_21
action_6 (35) = happyShift action_22
action_6 (36) = happyShift action_23
action_6 (37) = happyShift action_24
action_6 (39) = happyShift action_25
action_6 (40) = happyShift action_26
action_6 (41) = happyShift action_27
action_6 (42) = happyShift action_28
action_6 (43) = happyShift action_29
action_6 (45) = happyShift action_30
action_6 (46) = happyShift action_31
action_6 (47) = happyShift action_9
action_6 (11) = happyGoto action_14
action_6 (15) = happyGoto action_15
action_6 (16) = happyGoto action_16
action_6 (17) = happyGoto action_17
action_6 (18) = happyGoto action_18
action_6 _ = happyFail (happyExpListPerState 6)

action_7 (20) = happyShift action_12
action_7 (30) = happyShift action_13
action_7 (47) = happyShift action_9
action_7 (11) = happyGoto action_10
action_7 (19) = happyGoto action_11
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (47) = happyShift action_9
action_8 _ = happyFail (happyExpListPerState 8)

action_9 _ = happyReduce_8

action_10 _ = happyReduce_38

action_11 (48) = happyAccept
action_11 _ = happyFail (happyExpListPerState 11)

action_12 (20) = happyShift action_12
action_12 (30) = happyShift action_13
action_12 (47) = happyShift action_9
action_12 (11) = happyGoto action_10
action_12 (19) = happyGoto action_60
action_12 _ = happyFail (happyExpListPerState 12)

action_13 _ = happyReduce_37

action_14 _ = happyReduce_29

action_15 _ = happyReduce_36

action_16 (20) = happyShift action_19
action_16 (28) = happyShift action_20
action_16 (29) = happyShift action_21
action_16 (36) = happyShift action_23
action_16 (37) = happyShift action_24
action_16 (38) = happyShift action_58
action_16 (42) = happyShift action_28
action_16 (43) = happyShift action_29
action_16 (44) = happyShift action_59
action_16 (45) = happyShift action_30
action_16 (46) = happyShift action_31
action_16 (47) = happyShift action_9
action_16 (11) = happyGoto action_14
action_16 (17) = happyGoto action_47
action_16 _ = happyReduce_21

action_17 _ = happyReduce_23

action_18 (48) = happyAccept
action_18 _ = happyFail (happyExpListPerState 18)

action_19 (20) = happyShift action_19
action_19 (28) = happyShift action_20
action_19 (29) = happyShift action_21
action_19 (35) = happyShift action_22
action_19 (36) = happyShift action_23
action_19 (37) = happyShift action_24
action_19 (39) = happyShift action_25
action_19 (40) = happyShift action_26
action_19 (41) = happyShift action_27
action_19 (42) = happyShift action_28
action_19 (43) = happyShift action_29
action_19 (45) = happyShift action_30
action_19 (46) = happyShift action_31
action_19 (47) = happyShift action_9
action_19 (11) = happyGoto action_14
action_19 (15) = happyGoto action_57
action_19 (16) = happyGoto action_16
action_19 (17) = happyGoto action_17
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (20) = happyShift action_56
action_20 _ = happyFail (happyExpListPerState 20)

action_21 (20) = happyShift action_55
action_21 _ = happyFail (happyExpListPerState 21)

action_22 (20) = happyShift action_12
action_22 (30) = happyShift action_13
action_22 (47) = happyShift action_9
action_22 (11) = happyGoto action_10
action_22 (19) = happyGoto action_54
action_22 _ = happyFail (happyExpListPerState 22)

action_23 (20) = happyShift action_53
action_23 _ = happyFail (happyExpListPerState 23)

action_24 _ = happyReduce_28

action_25 (20) = happyShift action_52
action_25 _ = happyFail (happyExpListPerState 25)

action_26 (20) = happyShift action_51
action_26 _ = happyFail (happyExpListPerState 26)

action_27 (20) = happyShift action_12
action_27 (30) = happyShift action_13
action_27 (47) = happyShift action_9
action_27 (11) = happyGoto action_10
action_27 (19) = happyGoto action_50
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (20) = happyShift action_19
action_28 (28) = happyShift action_20
action_28 (29) = happyShift action_21
action_28 (36) = happyShift action_23
action_28 (37) = happyShift action_24
action_28 (42) = happyShift action_28
action_28 (43) = happyShift action_29
action_28 (45) = happyShift action_30
action_28 (46) = happyShift action_31
action_28 (47) = happyShift action_9
action_28 (11) = happyGoto action_14
action_28 (17) = happyGoto action_49
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (20) = happyShift action_19
action_29 (28) = happyShift action_20
action_29 (29) = happyShift action_21
action_29 (36) = happyShift action_23
action_29 (37) = happyShift action_24
action_29 (42) = happyShift action_28
action_29 (43) = happyShift action_29
action_29 (45) = happyShift action_30
action_29 (46) = happyShift action_31
action_29 (47) = happyShift action_9
action_29 (11) = happyGoto action_14
action_29 (17) = happyGoto action_48
action_29 _ = happyFail (happyExpListPerState 29)

action_30 _ = happyReduce_26

action_31 _ = happyReduce_27

action_32 (48) = happyAccept
action_32 _ = happyFail (happyExpListPerState 32)

action_33 (20) = happyShift action_19
action_33 (28) = happyShift action_20
action_33 (29) = happyShift action_21
action_33 (36) = happyShift action_23
action_33 (37) = happyShift action_24
action_33 (42) = happyShift action_28
action_33 (43) = happyShift action_29
action_33 (45) = happyShift action_30
action_33 (46) = happyShift action_31
action_33 (47) = happyShift action_9
action_33 (48) = happyAccept
action_33 (11) = happyGoto action_14
action_33 (17) = happyGoto action_47
action_33 _ = happyFail (happyExpListPerState 33)

action_34 (48) = happyAccept
action_34 _ = happyFail (happyExpListPerState 34)

action_35 (48) = happyAccept
action_35 _ = happyFail (happyExpListPerState 35)

action_36 (20) = happyShift action_19
action_36 (28) = happyShift action_20
action_36 (29) = happyShift action_21
action_36 (35) = happyShift action_22
action_36 (36) = happyShift action_23
action_36 (37) = happyShift action_24
action_36 (39) = happyShift action_25
action_36 (40) = happyShift action_26
action_36 (41) = happyShift action_27
action_36 (42) = happyShift action_28
action_36 (43) = happyShift action_29
action_36 (45) = happyShift action_30
action_36 (46) = happyShift action_31
action_36 (47) = happyShift action_9
action_36 (11) = happyGoto action_14
action_36 (15) = happyGoto action_46
action_36 (16) = happyGoto action_16
action_36 (17) = happyGoto action_17
action_36 _ = happyFail (happyExpListPerState 36)

action_37 (20) = happyShift action_19
action_37 (28) = happyShift action_20
action_37 (29) = happyShift action_21
action_37 (35) = happyShift action_22
action_37 (36) = happyShift action_23
action_37 (37) = happyShift action_24
action_37 (39) = happyShift action_25
action_37 (40) = happyShift action_26
action_37 (41) = happyShift action_27
action_37 (42) = happyShift action_28
action_37 (43) = happyShift action_29
action_37 (45) = happyShift action_30
action_37 (46) = happyShift action_31
action_37 (47) = happyShift action_9
action_37 (11) = happyGoto action_14
action_37 (15) = happyGoto action_45
action_37 (16) = happyGoto action_16
action_37 (17) = happyGoto action_17
action_37 _ = happyFail (happyExpListPerState 37)

action_38 (47) = happyShift action_9
action_38 (11) = happyGoto action_44
action_38 _ = happyFail (happyExpListPerState 38)

action_39 (48) = happyAccept
action_39 _ = happyFail (happyExpListPerState 39)

action_40 (26) = happyShift action_43
action_40 _ = happyFail (happyExpListPerState 40)

action_41 (48) = happyAccept
action_41 _ = happyFail (happyExpListPerState 41)

action_42 _ = happyReduce_9

action_43 (31) = happyShift action_36
action_43 (32) = happyShift action_37
action_43 (33) = happyShift action_38
action_43 (13) = happyGoto action_76
action_43 (14) = happyGoto action_40
action_43 _ = happyReduce_10

action_44 (24) = happyShift action_75
action_44 _ = happyFail (happyExpListPerState 44)

action_45 _ = happyReduce_13

action_46 (24) = happyShift action_74
action_46 _ = happyFail (happyExpListPerState 46)

action_47 _ = happyReduce_22

action_48 _ = happyReduce_25

action_49 _ = happyReduce_24

action_50 (23) = happyShift action_73
action_50 _ = happyFail (happyExpListPerState 50)

action_51 (20) = happyShift action_12
action_51 (30) = happyShift action_13
action_51 (47) = happyShift action_9
action_51 (11) = happyGoto action_10
action_51 (19) = happyGoto action_72
action_51 _ = happyFail (happyExpListPerState 51)

action_52 (20) = happyShift action_12
action_52 (30) = happyShift action_13
action_52 (47) = happyShift action_9
action_52 (11) = happyGoto action_10
action_52 (19) = happyGoto action_71
action_52 _ = happyFail (happyExpListPerState 52)

action_53 (20) = happyShift action_19
action_53 (28) = happyShift action_20
action_53 (29) = happyShift action_21
action_53 (35) = happyShift action_22
action_53 (36) = happyShift action_23
action_53 (37) = happyShift action_24
action_53 (39) = happyShift action_25
action_53 (40) = happyShift action_26
action_53 (41) = happyShift action_27
action_53 (42) = happyShift action_28
action_53 (43) = happyShift action_29
action_53 (45) = happyShift action_30
action_53 (46) = happyShift action_31
action_53 (47) = happyShift action_9
action_53 (11) = happyGoto action_14
action_53 (15) = happyGoto action_70
action_53 (16) = happyGoto action_16
action_53 (17) = happyGoto action_17
action_53 _ = happyFail (happyExpListPerState 53)

action_54 (27) = happyShift action_69
action_54 _ = happyFail (happyExpListPerState 54)

action_55 (20) = happyShift action_19
action_55 (28) = happyShift action_20
action_55 (29) = happyShift action_21
action_55 (35) = happyShift action_22
action_55 (36) = happyShift action_23
action_55 (37) = happyShift action_24
action_55 (39) = happyShift action_25
action_55 (40) = happyShift action_26
action_55 (41) = happyShift action_27
action_55 (42) = happyShift action_28
action_55 (43) = happyShift action_29
action_55 (45) = happyShift action_30
action_55 (46) = happyShift action_31
action_55 (47) = happyShift action_9
action_55 (11) = happyGoto action_14
action_55 (15) = happyGoto action_68
action_55 (16) = happyGoto action_16
action_55 (17) = happyGoto action_17
action_55 _ = happyFail (happyExpListPerState 55)

action_56 (20) = happyShift action_19
action_56 (28) = happyShift action_20
action_56 (29) = happyShift action_21
action_56 (35) = happyShift action_22
action_56 (36) = happyShift action_23
action_56 (37) = happyShift action_24
action_56 (39) = happyShift action_25
action_56 (40) = happyShift action_26
action_56 (41) = happyShift action_27
action_56 (42) = happyShift action_28
action_56 (43) = happyShift action_29
action_56 (45) = happyShift action_30
action_56 (46) = happyShift action_31
action_56 (47) = happyShift action_9
action_56 (11) = happyGoto action_14
action_56 (15) = happyGoto action_67
action_56 (16) = happyGoto action_16
action_56 (17) = happyGoto action_17
action_56 _ = happyFail (happyExpListPerState 56)

action_57 (21) = happyShift action_64
action_57 (22) = happyShift action_65
action_57 (24) = happyShift action_66
action_57 _ = happyFail (happyExpListPerState 57)

action_58 (20) = happyShift action_19
action_58 (28) = happyShift action_20
action_58 (29) = happyShift action_21
action_58 (35) = happyShift action_22
action_58 (36) = happyShift action_23
action_58 (37) = happyShift action_24
action_58 (39) = happyShift action_25
action_58 (40) = happyShift action_26
action_58 (41) = happyShift action_27
action_58 (42) = happyShift action_28
action_58 (43) = happyShift action_29
action_58 (45) = happyShift action_30
action_58 (46) = happyShift action_31
action_58 (47) = happyShift action_9
action_58 (11) = happyGoto action_14
action_58 (15) = happyGoto action_63
action_58 (16) = happyGoto action_16
action_58 (17) = happyGoto action_17
action_58 _ = happyFail (happyExpListPerState 58)

action_59 (20) = happyShift action_19
action_59 (28) = happyShift action_20
action_59 (29) = happyShift action_21
action_59 (35) = happyShift action_22
action_59 (36) = happyShift action_23
action_59 (37) = happyShift action_24
action_59 (39) = happyShift action_25
action_59 (40) = happyShift action_26
action_59 (41) = happyShift action_27
action_59 (42) = happyShift action_28
action_59 (43) = happyShift action_29
action_59 (45) = happyShift action_30
action_59 (46) = happyShift action_31
action_59 (47) = happyShift action_9
action_59 (11) = happyGoto action_14
action_59 (15) = happyGoto action_62
action_59 (16) = happyGoto action_16
action_59 (17) = happyGoto action_17
action_59 _ = happyFail (happyExpListPerState 59)

action_60 (22) = happyShift action_61
action_60 _ = happyFail (happyExpListPerState 60)

action_61 (20) = happyShift action_12
action_61 (30) = happyShift action_13
action_61 (47) = happyShift action_9
action_61 (11) = happyGoto action_10
action_61 (19) = happyGoto action_88
action_61 _ = happyFail (happyExpListPerState 61)

action_62 _ = happyReduce_19

action_63 _ = happyReduce_20

action_64 _ = happyReduce_35

action_65 (20) = happyShift action_19
action_65 (28) = happyShift action_20
action_65 (29) = happyShift action_21
action_65 (35) = happyShift action_22
action_65 (36) = happyShift action_23
action_65 (37) = happyShift action_24
action_65 (39) = happyShift action_25
action_65 (40) = happyShift action_26
action_65 (41) = happyShift action_27
action_65 (42) = happyShift action_28
action_65 (43) = happyShift action_29
action_65 (45) = happyShift action_30
action_65 (46) = happyShift action_31
action_65 (47) = happyShift action_9
action_65 (11) = happyGoto action_14
action_65 (15) = happyGoto action_87
action_65 (16) = happyGoto action_16
action_65 (17) = happyGoto action_17
action_65 _ = happyFail (happyExpListPerState 65)

action_66 (20) = happyShift action_19
action_66 (28) = happyShift action_20
action_66 (29) = happyShift action_21
action_66 (35) = happyShift action_22
action_66 (36) = happyShift action_23
action_66 (37) = happyShift action_24
action_66 (39) = happyShift action_25
action_66 (40) = happyShift action_26
action_66 (41) = happyShift action_27
action_66 (42) = happyShift action_28
action_66 (43) = happyShift action_29
action_66 (45) = happyShift action_30
action_66 (46) = happyShift action_31
action_66 (47) = happyShift action_9
action_66 (11) = happyGoto action_14
action_66 (15) = happyGoto action_86
action_66 (16) = happyGoto action_16
action_66 (17) = happyGoto action_17
action_66 _ = happyFail (happyExpListPerState 66)

action_67 (22) = happyShift action_85
action_67 _ = happyFail (happyExpListPerState 67)

action_68 (22) = happyShift action_84
action_68 _ = happyFail (happyExpListPerState 68)

action_69 (20) = happyShift action_19
action_69 (28) = happyShift action_20
action_69 (29) = happyShift action_21
action_69 (35) = happyShift action_22
action_69 (36) = happyShift action_23
action_69 (37) = happyShift action_24
action_69 (39) = happyShift action_25
action_69 (40) = happyShift action_26
action_69 (41) = happyShift action_27
action_69 (42) = happyShift action_28
action_69 (43) = happyShift action_29
action_69 (45) = happyShift action_30
action_69 (46) = happyShift action_31
action_69 (47) = happyShift action_9
action_69 (11) = happyGoto action_14
action_69 (15) = happyGoto action_83
action_69 (16) = happyGoto action_16
action_69 (17) = happyGoto action_17
action_69 _ = happyFail (happyExpListPerState 69)

action_70 (21) = happyShift action_82
action_70 _ = happyFail (happyExpListPerState 70)

action_71 (24) = happyShift action_81
action_71 _ = happyFail (happyExpListPerState 71)

action_72 (24) = happyShift action_80
action_72 _ = happyFail (happyExpListPerState 72)

action_73 (20) = happyShift action_19
action_73 (28) = happyShift action_20
action_73 (29) = happyShift action_21
action_73 (35) = happyShift action_22
action_73 (36) = happyShift action_23
action_73 (37) = happyShift action_24
action_73 (39) = happyShift action_25
action_73 (40) = happyShift action_26
action_73 (41) = happyShift action_27
action_73 (42) = happyShift action_28
action_73 (43) = happyShift action_29
action_73 (45) = happyShift action_30
action_73 (46) = happyShift action_31
action_73 (47) = happyShift action_9
action_73 (11) = happyGoto action_14
action_73 (15) = happyGoto action_15
action_73 (16) = happyGoto action_16
action_73 (17) = happyGoto action_17
action_73 (18) = happyGoto action_79
action_73 _ = happyFail (happyExpListPerState 73)

action_74 (20) = happyShift action_19
action_74 (28) = happyShift action_20
action_74 (29) = happyShift action_21
action_74 (35) = happyShift action_22
action_74 (36) = happyShift action_23
action_74 (37) = happyShift action_24
action_74 (39) = happyShift action_25
action_74 (40) = happyShift action_26
action_74 (41) = happyShift action_27
action_74 (42) = happyShift action_28
action_74 (43) = happyShift action_29
action_74 (45) = happyShift action_30
action_74 (46) = happyShift action_31
action_74 (47) = happyShift action_9
action_74 (11) = happyGoto action_14
action_74 (15) = happyGoto action_78
action_74 (16) = happyGoto action_16
action_74 (17) = happyGoto action_17
action_74 _ = happyFail (happyExpListPerState 74)

action_75 (20) = happyShift action_19
action_75 (28) = happyShift action_20
action_75 (29) = happyShift action_21
action_75 (35) = happyShift action_22
action_75 (36) = happyShift action_23
action_75 (37) = happyShift action_24
action_75 (39) = happyShift action_25
action_75 (40) = happyShift action_26
action_75 (41) = happyShift action_27
action_75 (42) = happyShift action_28
action_75 (43) = happyShift action_29
action_75 (45) = happyShift action_30
action_75 (46) = happyShift action_31
action_75 (47) = happyShift action_9
action_75 (11) = happyGoto action_14
action_75 (15) = happyGoto action_77
action_75 (16) = happyGoto action_16
action_75 (17) = happyGoto action_17
action_75 _ = happyFail (happyExpListPerState 75)

action_76 _ = happyReduce_11

action_77 (25) = happyShift action_97
action_77 _ = happyFail (happyExpListPerState 77)

action_78 _ = happyReduce_12

action_79 _ = happyReduce_17

action_80 (20) = happyShift action_19
action_80 (28) = happyShift action_20
action_80 (29) = happyShift action_21
action_80 (35) = happyShift action_22
action_80 (36) = happyShift action_23
action_80 (37) = happyShift action_24
action_80 (39) = happyShift action_25
action_80 (40) = happyShift action_26
action_80 (41) = happyShift action_27
action_80 (42) = happyShift action_28
action_80 (43) = happyShift action_29
action_80 (45) = happyShift action_30
action_80 (46) = happyShift action_31
action_80 (47) = happyShift action_9
action_80 (11) = happyGoto action_14
action_80 (15) = happyGoto action_96
action_80 (16) = happyGoto action_16
action_80 (17) = happyGoto action_17
action_80 _ = happyFail (happyExpListPerState 80)

action_81 (20) = happyShift action_19
action_81 (28) = happyShift action_20
action_81 (29) = happyShift action_21
action_81 (35) = happyShift action_22
action_81 (36) = happyShift action_23
action_81 (37) = happyShift action_24
action_81 (39) = happyShift action_25
action_81 (40) = happyShift action_26
action_81 (41) = happyShift action_27
action_81 (42) = happyShift action_28
action_81 (43) = happyShift action_29
action_81 (45) = happyShift action_30
action_81 (46) = happyShift action_31
action_81 (47) = happyShift action_9
action_81 (11) = happyGoto action_14
action_81 (15) = happyGoto action_95
action_81 (16) = happyGoto action_16
action_81 (17) = happyGoto action_17
action_81 _ = happyFail (happyExpListPerState 81)

action_82 _ = happyReduce_31

action_83 (34) = happyShift action_94
action_83 _ = happyFail (happyExpListPerState 83)

action_84 (20) = happyShift action_19
action_84 (28) = happyShift action_20
action_84 (29) = happyShift action_21
action_84 (35) = happyShift action_22
action_84 (36) = happyShift action_23
action_84 (37) = happyShift action_24
action_84 (39) = happyShift action_25
action_84 (40) = happyShift action_26
action_84 (41) = happyShift action_27
action_84 (42) = happyShift action_28
action_84 (43) = happyShift action_29
action_84 (45) = happyShift action_30
action_84 (46) = happyShift action_31
action_84 (47) = happyShift action_9
action_84 (11) = happyGoto action_14
action_84 (15) = happyGoto action_93
action_84 (16) = happyGoto action_16
action_84 (17) = happyGoto action_17
action_84 _ = happyFail (happyExpListPerState 84)

action_85 (20) = happyShift action_19
action_85 (28) = happyShift action_20
action_85 (29) = happyShift action_21
action_85 (35) = happyShift action_22
action_85 (36) = happyShift action_23
action_85 (37) = happyShift action_24
action_85 (39) = happyShift action_25
action_85 (40) = happyShift action_26
action_85 (41) = happyShift action_27
action_85 (42) = happyShift action_28
action_85 (43) = happyShift action_29
action_85 (45) = happyShift action_30
action_85 (46) = happyShift action_31
action_85 (47) = happyShift action_9
action_85 (11) = happyGoto action_14
action_85 (15) = happyGoto action_92
action_85 (16) = happyGoto action_16
action_85 (17) = happyGoto action_17
action_85 _ = happyFail (happyExpListPerState 85)

action_86 (21) = happyShift action_91
action_86 _ = happyFail (happyExpListPerState 86)

action_87 (21) = happyShift action_90
action_87 _ = happyFail (happyExpListPerState 87)

action_88 (21) = happyShift action_89
action_88 _ = happyFail (happyExpListPerState 88)

action_89 _ = happyReduce_39

action_90 _ = happyReduce_33

action_91 _ = happyReduce_34

action_92 (22) = happyShift action_103
action_92 _ = happyFail (happyExpListPerState 92)

action_93 (22) = happyShift action_102
action_93 _ = happyFail (happyExpListPerState 93)

action_94 (20) = happyShift action_19
action_94 (28) = happyShift action_20
action_94 (29) = happyShift action_21
action_94 (35) = happyShift action_22
action_94 (36) = happyShift action_23
action_94 (37) = happyShift action_24
action_94 (39) = happyShift action_25
action_94 (40) = happyShift action_26
action_94 (41) = happyShift action_27
action_94 (42) = happyShift action_28
action_94 (43) = happyShift action_29
action_94 (45) = happyShift action_30
action_94 (46) = happyShift action_31
action_94 (47) = happyShift action_9
action_94 (11) = happyGoto action_14
action_94 (15) = happyGoto action_15
action_94 (16) = happyGoto action_16
action_94 (17) = happyGoto action_17
action_94 (18) = happyGoto action_101
action_94 _ = happyFail (happyExpListPerState 94)

action_95 (21) = happyShift action_100
action_95 _ = happyFail (happyExpListPerState 95)

action_96 (21) = happyShift action_99
action_96 _ = happyFail (happyExpListPerState 96)

action_97 (20) = happyShift action_19
action_97 (28) = happyShift action_20
action_97 (29) = happyShift action_21
action_97 (35) = happyShift action_22
action_97 (36) = happyShift action_23
action_97 (37) = happyShift action_24
action_97 (39) = happyShift action_25
action_97 (40) = happyShift action_26
action_97 (41) = happyShift action_27
action_97 (42) = happyShift action_28
action_97 (43) = happyShift action_29
action_97 (45) = happyShift action_30
action_97 (46) = happyShift action_31
action_97 (47) = happyShift action_9
action_97 (11) = happyGoto action_14
action_97 (15) = happyGoto action_98
action_97 (16) = happyGoto action_16
action_97 (17) = happyGoto action_17
action_97 _ = happyFail (happyExpListPerState 97)

action_98 _ = happyReduce_14

action_99 (38) = happyShift action_107
action_99 _ = happyFail (happyExpListPerState 99)

action_100 (44) = happyShift action_106
action_100 _ = happyFail (happyExpListPerState 100)

action_101 _ = happyReduce_18

action_102 (20) = happyShift action_19
action_102 (28) = happyShift action_20
action_102 (29) = happyShift action_21
action_102 (35) = happyShift action_22
action_102 (36) = happyShift action_23
action_102 (37) = happyShift action_24
action_102 (39) = happyShift action_25
action_102 (40) = happyShift action_26
action_102 (41) = happyShift action_27
action_102 (42) = happyShift action_28
action_102 (43) = happyShift action_29
action_102 (45) = happyShift action_30
action_102 (46) = happyShift action_31
action_102 (47) = happyShift action_9
action_102 (11) = happyGoto action_14
action_102 (15) = happyGoto action_105
action_102 (16) = happyGoto action_16
action_102 (17) = happyGoto action_17
action_102 _ = happyFail (happyExpListPerState 102)

action_103 (20) = happyShift action_19
action_103 (28) = happyShift action_20
action_103 (29) = happyShift action_21
action_103 (35) = happyShift action_22
action_103 (36) = happyShift action_23
action_103 (37) = happyShift action_24
action_103 (39) = happyShift action_25
action_103 (40) = happyShift action_26
action_103 (41) = happyShift action_27
action_103 (42) = happyShift action_28
action_103 (43) = happyShift action_29
action_103 (45) = happyShift action_30
action_103 (46) = happyShift action_31
action_103 (47) = happyShift action_9
action_103 (11) = happyGoto action_14
action_103 (15) = happyGoto action_104
action_103 (16) = happyGoto action_16
action_103 (17) = happyGoto action_17
action_103 _ = happyFail (happyExpListPerState 103)

action_104 (21) = happyShift action_111
action_104 _ = happyFail (happyExpListPerState 104)

action_105 (21) = happyShift action_110
action_105 _ = happyFail (happyExpListPerState 105)

action_106 (20) = happyShift action_19
action_106 (28) = happyShift action_20
action_106 (29) = happyShift action_21
action_106 (35) = happyShift action_22
action_106 (36) = happyShift action_23
action_106 (37) = happyShift action_24
action_106 (39) = happyShift action_25
action_106 (40) = happyShift action_26
action_106 (41) = happyShift action_27
action_106 (42) = happyShift action_28
action_106 (43) = happyShift action_29
action_106 (45) = happyShift action_30
action_106 (46) = happyShift action_31
action_106 (47) = happyShift action_9
action_106 (11) = happyGoto action_14
action_106 (15) = happyGoto action_15
action_106 (16) = happyGoto action_16
action_106 (17) = happyGoto action_17
action_106 (18) = happyGoto action_109
action_106 _ = happyFail (happyExpListPerState 106)

action_107 (20) = happyShift action_19
action_107 (28) = happyShift action_20
action_107 (29) = happyShift action_21
action_107 (35) = happyShift action_22
action_107 (36) = happyShift action_23
action_107 (37) = happyShift action_24
action_107 (39) = happyShift action_25
action_107 (40) = happyShift action_26
action_107 (41) = happyShift action_27
action_107 (42) = happyShift action_28
action_107 (43) = happyShift action_29
action_107 (45) = happyShift action_30
action_107 (46) = happyShift action_31
action_107 (47) = happyShift action_9
action_107 (11) = happyGoto action_14
action_107 (15) = happyGoto action_15
action_107 (16) = happyGoto action_16
action_107 (17) = happyGoto action_17
action_107 (18) = happyGoto action_108
action_107 _ = happyFail (happyExpListPerState 107)

action_108 _ = happyReduce_16

action_109 _ = happyReduce_15

action_110 _ = happyReduce_32

action_111 _ = happyReduce_30

happyReduce_8 = happySpecReduce_1  11 happyReduction_8
happyReduction_8 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn11
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.VarIdent (tokenText happy_var_1))
	)
happyReduction_8 _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_1  12 happyReduction_9
happyReduction_9 (HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn12
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AProgram (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_9 _  = notHappyAtAll 

happyReduce_10 = happySpecReduce_0  13 happyReduction_10
happyReduction_10  =  HappyAbsSyn13
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_11 = happySpecReduce_3  13 happyReduction_11
happyReduction_11 (HappyAbsSyn13  happy_var_3)
	_
	(HappyAbsSyn14  happy_var_1)
	 =  HappyAbsSyn13
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_11 _ _ _  = notHappyAtAll 

happyReduce_12 = happyReduce 4 14 happyReduction_12
happyReduction_12 ((HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn14
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.CommandCheck (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_13 = happySpecReduce_2  14 happyReduction_13
happyReduction_13 (HappyAbsSyn15  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn14
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.CommandCompute (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_13 _ _  = notHappyAtAll 

happyReduce_14 = happyReduce 6 14 happyReduction_14
happyReduction_14 ((HappyAbsSyn15  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn14
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.CommandDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_15 = happyReduce 8 15 happyReduction_15
happyReduction_15 ((HappyAbsSyn18  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pi (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_16 = happyReduce 8 15 happyReduction_16
happyReduction_16 ((HappyAbsSyn18  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Sigma (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_17 = happyReduce 4 15 happyReduction_17
happyReduction_17 ((HappyAbsSyn18  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Lam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_18 = happyReduce 6 15 happyReduction_18
happyReduction_18 ((HappyAbsSyn18  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Let (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_19 = happySpecReduce_3  15 happyReduction_19
happyReduction_19 (HappyAbsSyn15  happy_var_3)
	_
	(HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Arrow (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_19 _ _ _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_3  15 happyReduction_20
happyReduction_20 (HappyAbsSyn15  happy_var_3)
	_
	(HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Product (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_20 _ _ _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_1  15 happyReduction_21
happyReduction_21 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_21 _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_2  16 happyReduction_22
happyReduction_22 (HappyAbsSyn15  happy_var_2)
	(HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.App (fst happy_var_1) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_22 _ _  = notHappyAtAll 

happyReduce_23 = happySpecReduce_1  16 happyReduction_23
happyReduction_23 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_23 _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_2  17 happyReduction_24
happyReduction_24 (HappyAbsSyn15  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.First (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_24 _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_2  17 happyReduction_25
happyReduction_25 (HappyAbsSyn15  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Second (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_25 _ _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_1  17 happyReduction_26
happyReduction_26 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Universe (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_26 _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_1  17 happyReduction_27
happyReduction_27 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_27 _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_1  17 happyReduction_28
happyReduction_28 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitVal (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_28 _  = notHappyAtAll 

happyReduce_29 = happySpecReduce_1  17 happyReduction_29
happyReduction_29 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn15
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Var (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_29 _  = notHappyAtAll 

happyReduce_30 = happyReduce 8 17 happyReduction_30
happyReduction_30 (_ `HappyStk`
	(HappyAbsSyn15  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.IdType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_31 = happyReduce 4 17 happyReduction_31
happyReduction_31 (_ `HappyStk`
	(HappyAbsSyn15  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Refl (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_32 = happyReduce 8 17 happyReduction_32
happyReduction_32 (_ `HappyStk`
	(HappyAbsSyn15  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.J (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_33 = happyReduce 5 17 happyReduction_33
happyReduction_33 (_ `HappyStk`
	(HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_34 = happyReduce 5 17 happyReduction_34
happyReduction_34 (_ `HappyStk`
	(HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Ann (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_35 = happySpecReduce_3  17 happyReduction_35
happyReduction_35 _
	(HappyAbsSyn15  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), (snd happy_var_2))
	)
happyReduction_35 _ _ _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_1  18 happyReduction_36
happyReduction_36 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn18
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AScopedTerm (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_36 _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_1  19 happyReduction_37
happyReduction_37 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn19
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternWildcard (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_37 _  = notHappyAtAll 

happyReduce_38 = happySpecReduce_1  19 happyReduction_38
happyReduction_38 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn19
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.PatternVar (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_38 _  = notHappyAtAll 

happyReduce_39 = happyReduce 5 19 happyReduction_39
happyReduction_39 (_ `HappyStk`
	(HappyAbsSyn19  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternPair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyNewToken action sts stk [] =
	action 48 48 notHappyAtAll (HappyState action) sts stk []

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
	PT _ (TS _ 17) -> cont 36;
	PT _ (TS _ 18) -> cont 37;
	PT _ (TS _ 19) -> cont 38;
	PT _ (TS _ 20) -> cont 39;
	PT _ (TS _ 21) -> cont 40;
	PT _ (TS _ 22) -> cont 41;
	PT _ (TS _ 23) -> cont 42;
	PT _ (TS _ 24) -> cont 43;
	PT _ (TS _ 25) -> cont 44;
	PT _ (TS _ 26) -> cont 45;
	PT _ (TS _ 27) -> cont 46;
	PT _ (T_VarIdent _) -> cont 47;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 48 tk tks = happyError' (tks, explist)
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
pProgram_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn12 z -> happyReturn z; _other -> notHappyAtAll })

pListCommand_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn13 z -> happyReturn z; _other -> notHappyAtAll })

pCommand_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_2 tks) (\x -> case x of {HappyAbsSyn14 z -> happyReturn z; _other -> notHappyAtAll })

pTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_3 tks) (\x -> case x of {HappyAbsSyn15 z -> happyReturn z; _other -> notHappyAtAll })

pTerm1_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_4 tks) (\x -> case x of {HappyAbsSyn15 z -> happyReturn z; _other -> notHappyAtAll })

pTerm2_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_5 tks) (\x -> case x of {HappyAbsSyn15 z -> happyReturn z; _other -> notHappyAtAll })

pScopedTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_6 tks) (\x -> case x of {HappyAbsSyn18 z -> happyReturn z; _other -> notHappyAtAll })

pPattern_internal tks = happySomeParser where
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

-- Entrypoints

pProgram :: [Token] -> Err Language.MLTT.Syntax.Abs.Program
pProgram = fmap snd . pProgram_internal

pListCommand :: [Token] -> Err [Language.MLTT.Syntax.Abs.Command]
pListCommand = fmap snd . pListCommand_internal

pCommand :: [Token] -> Err Language.MLTT.Syntax.Abs.Command
pCommand = fmap snd . pCommand_internal

pTerm :: [Token] -> Err Language.MLTT.Syntax.Abs.Term
pTerm = fmap snd . pTerm_internal

pTerm1 :: [Token] -> Err Language.MLTT.Syntax.Abs.Term
pTerm1 = fmap snd . pTerm1_internal

pTerm2 :: [Token] -> Err Language.MLTT.Syntax.Abs.Term
pTerm2 = fmap snd . pTerm2_internal

pScopedTerm :: [Token] -> Err Language.MLTT.Syntax.Abs.ScopedTerm
pScopedTerm = fmap snd . pScopedTerm_internal

pPattern :: [Token] -> Err Language.MLTT.Syntax.Abs.Pattern
pPattern = fmap snd . pPattern_internal
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
