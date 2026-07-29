{-# OPTIONS_GHC -w #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.MLTT.Syntax.Par
  ( happyError
  , myLexer
  , pProgram
  , pListModule
  , pModule
  , pImport
  , pListImport
  , pDecl
  , pListDecl
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
	| HappyAbsSyn15 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.VarIdent))
	| HappyAbsSyn16 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Program))
	| HappyAbsSyn17 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Module]))
	| HappyAbsSyn18 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Module))
	| HappyAbsSyn19 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Import))
	| HappyAbsSyn20 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Import]))
	| HappyAbsSyn21 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Decl))
	| HappyAbsSyn22 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Decl]))
	| HappyAbsSyn23 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Term))
	| HappyAbsSyn26 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.ScopedTerm))
	| HappyAbsSyn27 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Pattern))

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
 action_111,
 action_112,
 action_113,
 action_114,
 action_115,
 action_116,
 action_117,
 action_118,
 action_119,
 action_120,
 action_121,
 action_122,
 action_123,
 action_124,
 action_125,
 action_126,
 action_127,
 action_128,
 action_129,
 action_130,
 action_131,
 action_132,
 action_133,
 action_134,
 action_135,
 action_136,
 action_137,
 action_138,
 action_139,
 action_140,
 action_141,
 action_142,
 action_143,
 action_144,
 action_145,
 action_146 :: () => Prelude.Int -> ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

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
 happyReduce_39,
 happyReduce_40,
 happyReduce_41,
 happyReduce_42,
 happyReduce_43,
 happyReduce_44,
 happyReduce_45,
 happyReduce_46,
 happyReduce_47,
 happyReduce_48,
 happyReduce_49,
 happyReduce_50,
 happyReduce_51,
 happyReduce_52,
 happyReduce_53 :: () => ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,324) ([0,0,2048,0,0,0,1024,0,0,0,512,0,0,0,32,0,0,0,16,0,0,0,903,0,0,32768,451,0,0,6160,49928,119,0,3080,384,59,0,1540,32960,29,0,770,63585,14,0,513,0,4,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,2048,16,8192,0,0,0,0,0,0,0,0,0,0,0,0,0,49280,6144,1009,0,0,0,0,0,0,0,0,0,6160,49928,119,0,8,0,0,0,4,0,0,0,1026,0,8,0,1,0,0,0,0,0,0,16384,0,0,0,8192,0,0,0,4096,32,16384,0,2048,32780,15105,0,1024,49158,7552,0,0,0,0,0,0,0,0,0,0,0,0,0,24640,3072,472,0,0,0,0,0,512,0,0,0,0,0,0,0,1540,61634,29,0,770,63585,14,0,0,0,4,0,0,0,2,0,0,0,1,0,512,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2048,0,0,0,0,0,0,0,0,0,0,0,256,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,2048,0,0,0,0,32768,0,0,0,0,0,0,0,2,0,8192,0,0,0,0,0,0,0,2048,0,0,0,0,1806,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,2052,0,16,0,1026,0,8,0,33153,31792,7,0,32,0,0,16384,8288,57100,1,8192,4144,61318,0,57344,0,0,0,2048,33804,15329,0,1024,49670,7664,0,2048,0,0,0,256,2,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,6160,49928,119,0,3080,57732,59,0,16,0,0,0,8,0,0,0,33153,31792,7,0,1,0,0,0,2,0,0,0,1,0,0,4096,2072,30659,0,0,0,0,0,1024,49670,7664,0,512,24835,3832,0,0,32768,0,0,1024,0,0,0,0,0,0,0,0,4,0,0,49152,225,0,0,3080,57732,59,0,28672,56,0,0,32,0,0,0,0,0,0,0,0,0,0,16384,8288,57100,1,8192,4144,61318,0,0,0,0,0,0,512,0,0,1024,49670,7664,0,512,24835,3832,0,512,0,0,0,256,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,8,0,0,0,33153,31792,7,0,1,0,0,32768,0,0,0,8192,4144,61318,0,0,0,16,0,32768,0,0,0,0,0,0,0,512,24835,3832,0,0,0,0,0,0,0,0,0,0,32768,0,0,0,0,16,0,0,0,0,0,3080,57732,59,0,1540,61634,29,0,4,0,0,0,2,0,0,32768,16576,48664,3,16384,8288,57100,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram_internal","%start_pListModule_internal","%start_pModule_internal","%start_pImport_internal","%start_pListImport_internal","%start_pDecl_internal","%start_pListDecl_internal","%start_pTerm_internal","%start_pTerm1_internal","%start_pTerm2_internal","%start_pScopedTerm_internal","%start_pPattern_internal","VarIdent","Program","ListModule","Module","Import","ListImport","Decl","ListDecl","Term","Term1","Term2","ScopedTerm","Pattern","'('","')'","','","':'","':='","';'","'='","'Id'","'J'","'_'","'check'","'compute'","'def'","'import'","'in'","'let'","'module'","'namespace'","'open'","'private'","'refl'","'tt'","'where'","'{'","'}'","'\215'","'\928'","'\931'","'\955'","'\960\8321'","'\960\8322'","'\8594'","'\120140'","'\120793'","L_VarIdent","%eof"]
        bit_start = st Prelude.* 63
        bit_end = (st Prelude.+ 1) Prelude.* 63
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..62]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (44) = happyShift action_53
action_0 (16) = happyGoto action_56
action_0 (17) = happyGoto action_57
action_0 (18) = happyGoto action_55
action_0 _ = happyReduce_14

action_1 (44) = happyShift action_53
action_1 (17) = happyGoto action_54
action_1 (18) = happyGoto action_55
action_1 _ = happyReduce_14

action_2 (44) = happyShift action_53
action_2 (18) = happyGoto action_52
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (41) = happyShift action_50
action_3 (19) = happyGoto action_51
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (41) = happyShift action_50
action_4 (19) = happyGoto action_48
action_4 (20) = happyGoto action_49
action_4 _ = happyReduce_18

action_5 (38) = happyShift action_41
action_5 (39) = happyShift action_42
action_5 (40) = happyShift action_43
action_5 (45) = happyShift action_44
action_5 (46) = happyShift action_45
action_5 (47) = happyShift action_46
action_5 (21) = happyGoto action_47
action_5 _ = happyFail (happyExpListPerState 5)

action_6 (38) = happyShift action_41
action_6 (39) = happyShift action_42
action_6 (40) = happyShift action_43
action_6 (45) = happyShift action_44
action_6 (46) = happyShift action_45
action_6 (47) = happyShift action_46
action_6 (21) = happyGoto action_39
action_6 (22) = happyGoto action_40
action_6 _ = happyReduce_26

action_7 (28) = happyShift action_23
action_7 (35) = happyShift action_24
action_7 (36) = happyShift action_25
action_7 (43) = happyShift action_26
action_7 (48) = happyShift action_27
action_7 (49) = happyShift action_28
action_7 (54) = happyShift action_29
action_7 (55) = happyShift action_30
action_7 (56) = happyShift action_31
action_7 (57) = happyShift action_32
action_7 (58) = happyShift action_33
action_7 (60) = happyShift action_34
action_7 (61) = happyShift action_35
action_7 (62) = happyShift action_13
action_7 (15) = happyGoto action_18
action_7 (23) = happyGoto action_38
action_7 (24) = happyGoto action_20
action_7 (25) = happyGoto action_21
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (28) = happyShift action_23
action_8 (35) = happyShift action_24
action_8 (36) = happyShift action_25
action_8 (48) = happyShift action_27
action_8 (49) = happyShift action_28
action_8 (57) = happyShift action_32
action_8 (58) = happyShift action_33
action_8 (60) = happyShift action_34
action_8 (61) = happyShift action_35
action_8 (62) = happyShift action_13
action_8 (15) = happyGoto action_18
action_8 (24) = happyGoto action_37
action_8 (25) = happyGoto action_21
action_8 _ = happyFail (happyExpListPerState 8)

action_9 (28) = happyShift action_23
action_9 (35) = happyShift action_24
action_9 (36) = happyShift action_25
action_9 (48) = happyShift action_27
action_9 (49) = happyShift action_28
action_9 (57) = happyShift action_32
action_9 (58) = happyShift action_33
action_9 (60) = happyShift action_34
action_9 (61) = happyShift action_35
action_9 (62) = happyShift action_13
action_9 (15) = happyGoto action_18
action_9 (25) = happyGoto action_36
action_9 _ = happyFail (happyExpListPerState 9)

action_10 (28) = happyShift action_23
action_10 (35) = happyShift action_24
action_10 (36) = happyShift action_25
action_10 (43) = happyShift action_26
action_10 (48) = happyShift action_27
action_10 (49) = happyShift action_28
action_10 (54) = happyShift action_29
action_10 (55) = happyShift action_30
action_10 (56) = happyShift action_31
action_10 (57) = happyShift action_32
action_10 (58) = happyShift action_33
action_10 (60) = happyShift action_34
action_10 (61) = happyShift action_35
action_10 (62) = happyShift action_13
action_10 (15) = happyGoto action_18
action_10 (23) = happyGoto action_19
action_10 (24) = happyGoto action_20
action_10 (25) = happyGoto action_21
action_10 (26) = happyGoto action_22
action_10 _ = happyFail (happyExpListPerState 10)

action_11 (28) = happyShift action_16
action_11 (37) = happyShift action_17
action_11 (62) = happyShift action_13
action_11 (15) = happyGoto action_14
action_11 (27) = happyGoto action_15
action_11 _ = happyFail (happyExpListPerState 11)

action_12 (62) = happyShift action_13
action_12 _ = happyFail (happyExpListPerState 12)

action_13 _ = happyReduce_12

action_14 _ = happyReduce_52

action_15 (63) = happyAccept
action_15 _ = happyFail (happyExpListPerState 15)

action_16 (28) = happyShift action_16
action_16 (37) = happyShift action_17
action_16 (62) = happyShift action_13
action_16 (15) = happyGoto action_14
action_16 (27) = happyGoto action_82
action_16 _ = happyFail (happyExpListPerState 16)

action_17 _ = happyReduce_51

action_18 _ = happyReduce_43

action_19 _ = happyReduce_50

action_20 (28) = happyShift action_23
action_20 (35) = happyShift action_24
action_20 (36) = happyShift action_25
action_20 (48) = happyShift action_27
action_20 (49) = happyShift action_28
action_20 (53) = happyShift action_80
action_20 (57) = happyShift action_32
action_20 (58) = happyShift action_33
action_20 (59) = happyShift action_81
action_20 (60) = happyShift action_34
action_20 (61) = happyShift action_35
action_20 (62) = happyShift action_13
action_20 (15) = happyGoto action_18
action_20 (25) = happyGoto action_69
action_20 _ = happyReduce_35

action_21 _ = happyReduce_37

action_22 (63) = happyAccept
action_22 _ = happyFail (happyExpListPerState 22)

action_23 (28) = happyShift action_23
action_23 (35) = happyShift action_24
action_23 (36) = happyShift action_25
action_23 (43) = happyShift action_26
action_23 (48) = happyShift action_27
action_23 (49) = happyShift action_28
action_23 (54) = happyShift action_29
action_23 (55) = happyShift action_30
action_23 (56) = happyShift action_31
action_23 (57) = happyShift action_32
action_23 (58) = happyShift action_33
action_23 (60) = happyShift action_34
action_23 (61) = happyShift action_35
action_23 (62) = happyShift action_13
action_23 (15) = happyGoto action_18
action_23 (23) = happyGoto action_79
action_23 (24) = happyGoto action_20
action_23 (25) = happyGoto action_21
action_23 _ = happyFail (happyExpListPerState 23)

action_24 (28) = happyShift action_78
action_24 _ = happyFail (happyExpListPerState 24)

action_25 (28) = happyShift action_77
action_25 _ = happyFail (happyExpListPerState 25)

action_26 (28) = happyShift action_16
action_26 (37) = happyShift action_17
action_26 (62) = happyShift action_13
action_26 (15) = happyGoto action_14
action_26 (27) = happyGoto action_76
action_26 _ = happyFail (happyExpListPerState 26)

action_27 (28) = happyShift action_75
action_27 _ = happyFail (happyExpListPerState 27)

action_28 _ = happyReduce_42

action_29 (28) = happyShift action_74
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (28) = happyShift action_73
action_30 _ = happyFail (happyExpListPerState 30)

action_31 (28) = happyShift action_16
action_31 (37) = happyShift action_17
action_31 (62) = happyShift action_13
action_31 (15) = happyGoto action_14
action_31 (27) = happyGoto action_72
action_31 _ = happyFail (happyExpListPerState 31)

action_32 (28) = happyShift action_23
action_32 (35) = happyShift action_24
action_32 (36) = happyShift action_25
action_32 (48) = happyShift action_27
action_32 (49) = happyShift action_28
action_32 (57) = happyShift action_32
action_32 (58) = happyShift action_33
action_32 (60) = happyShift action_34
action_32 (61) = happyShift action_35
action_32 (62) = happyShift action_13
action_32 (15) = happyGoto action_18
action_32 (25) = happyGoto action_71
action_32 _ = happyFail (happyExpListPerState 32)

action_33 (28) = happyShift action_23
action_33 (35) = happyShift action_24
action_33 (36) = happyShift action_25
action_33 (48) = happyShift action_27
action_33 (49) = happyShift action_28
action_33 (57) = happyShift action_32
action_33 (58) = happyShift action_33
action_33 (60) = happyShift action_34
action_33 (61) = happyShift action_35
action_33 (62) = happyShift action_13
action_33 (15) = happyGoto action_18
action_33 (25) = happyGoto action_70
action_33 _ = happyFail (happyExpListPerState 33)

action_34 _ = happyReduce_40

action_35 _ = happyReduce_41

action_36 (63) = happyAccept
action_36 _ = happyFail (happyExpListPerState 36)

action_37 (28) = happyShift action_23
action_37 (35) = happyShift action_24
action_37 (36) = happyShift action_25
action_37 (48) = happyShift action_27
action_37 (49) = happyShift action_28
action_37 (57) = happyShift action_32
action_37 (58) = happyShift action_33
action_37 (60) = happyShift action_34
action_37 (61) = happyShift action_35
action_37 (62) = happyShift action_13
action_37 (63) = happyAccept
action_37 (15) = happyGoto action_18
action_37 (25) = happyGoto action_69
action_37 _ = happyFail (happyExpListPerState 37)

action_38 (63) = happyAccept
action_38 _ = happyFail (happyExpListPerState 38)

action_39 (33) = happyShift action_68
action_39 _ = happyReduce_27

action_40 (63) = happyAccept
action_40 _ = happyFail (happyExpListPerState 40)

action_41 (28) = happyShift action_23
action_41 (35) = happyShift action_24
action_41 (36) = happyShift action_25
action_41 (43) = happyShift action_26
action_41 (48) = happyShift action_27
action_41 (49) = happyShift action_28
action_41 (54) = happyShift action_29
action_41 (55) = happyShift action_30
action_41 (56) = happyShift action_31
action_41 (57) = happyShift action_32
action_41 (58) = happyShift action_33
action_41 (60) = happyShift action_34
action_41 (61) = happyShift action_35
action_41 (62) = happyShift action_13
action_41 (15) = happyGoto action_18
action_41 (23) = happyGoto action_67
action_41 (24) = happyGoto action_20
action_41 (25) = happyGoto action_21
action_41 _ = happyFail (happyExpListPerState 41)

action_42 (28) = happyShift action_23
action_42 (35) = happyShift action_24
action_42 (36) = happyShift action_25
action_42 (43) = happyShift action_26
action_42 (48) = happyShift action_27
action_42 (49) = happyShift action_28
action_42 (54) = happyShift action_29
action_42 (55) = happyShift action_30
action_42 (56) = happyShift action_31
action_42 (57) = happyShift action_32
action_42 (58) = happyShift action_33
action_42 (60) = happyShift action_34
action_42 (61) = happyShift action_35
action_42 (62) = happyShift action_13
action_42 (15) = happyGoto action_18
action_42 (23) = happyGoto action_66
action_42 (24) = happyGoto action_20
action_42 (25) = happyGoto action_21
action_42 _ = happyFail (happyExpListPerState 42)

action_43 (62) = happyShift action_13
action_43 (15) = happyGoto action_65
action_43 _ = happyFail (happyExpListPerState 43)

action_44 (62) = happyShift action_13
action_44 (15) = happyGoto action_64
action_44 _ = happyFail (happyExpListPerState 44)

action_45 (62) = happyShift action_13
action_45 (15) = happyGoto action_63
action_45 _ = happyFail (happyExpListPerState 45)

action_46 (40) = happyShift action_62
action_46 _ = happyFail (happyExpListPerState 46)

action_47 (63) = happyAccept
action_47 _ = happyFail (happyExpListPerState 47)

action_48 (33) = happyShift action_61
action_48 _ = happyFail (happyExpListPerState 48)

action_49 (63) = happyAccept
action_49 _ = happyFail (happyExpListPerState 49)

action_50 (62) = happyShift action_13
action_50 (15) = happyGoto action_60
action_50 _ = happyFail (happyExpListPerState 50)

action_51 (63) = happyAccept
action_51 _ = happyFail (happyExpListPerState 51)

action_52 (63) = happyAccept
action_52 _ = happyFail (happyExpListPerState 52)

action_53 (62) = happyShift action_13
action_53 (15) = happyGoto action_59
action_53 _ = happyFail (happyExpListPerState 53)

action_54 (63) = happyAccept
action_54 _ = happyFail (happyExpListPerState 54)

action_55 (44) = happyShift action_53
action_55 (17) = happyGoto action_58
action_55 (18) = happyGoto action_55
action_55 _ = happyReduce_14

action_56 (63) = happyAccept
action_56 _ = happyFail (happyExpListPerState 56)

action_57 _ = happyReduce_13

action_58 _ = happyReduce_15

action_59 (33) = happyShift action_102
action_59 _ = happyFail (happyExpListPerState 59)

action_60 _ = happyReduce_17

action_61 (41) = happyShift action_50
action_61 (19) = happyGoto action_48
action_61 (20) = happyGoto action_101
action_61 _ = happyReduce_18

action_62 (62) = happyShift action_13
action_62 (15) = happyGoto action_100
action_62 _ = happyFail (happyExpListPerState 62)

action_63 _ = happyReduce_23

action_64 (50) = happyShift action_99
action_64 _ = happyFail (happyExpListPerState 64)

action_65 (31) = happyShift action_98
action_65 _ = happyFail (happyExpListPerState 65)

action_66 _ = happyReduce_25

action_67 (31) = happyShift action_97
action_67 _ = happyFail (happyExpListPerState 67)

action_68 (38) = happyShift action_41
action_68 (39) = happyShift action_42
action_68 (40) = happyShift action_43
action_68 (45) = happyShift action_44
action_68 (46) = happyShift action_45
action_68 (47) = happyShift action_46
action_68 (21) = happyGoto action_39
action_68 (22) = happyGoto action_96
action_68 _ = happyReduce_26

action_69 _ = happyReduce_36

action_70 _ = happyReduce_39

action_71 _ = happyReduce_38

action_72 (59) = happyShift action_95
action_72 _ = happyFail (happyExpListPerState 72)

action_73 (28) = happyShift action_16
action_73 (37) = happyShift action_17
action_73 (62) = happyShift action_13
action_73 (15) = happyGoto action_14
action_73 (27) = happyGoto action_94
action_73 _ = happyFail (happyExpListPerState 73)

action_74 (28) = happyShift action_16
action_74 (37) = happyShift action_17
action_74 (62) = happyShift action_13
action_74 (15) = happyGoto action_14
action_74 (27) = happyGoto action_93
action_74 _ = happyFail (happyExpListPerState 74)

action_75 (28) = happyShift action_23
action_75 (35) = happyShift action_24
action_75 (36) = happyShift action_25
action_75 (43) = happyShift action_26
action_75 (48) = happyShift action_27
action_75 (49) = happyShift action_28
action_75 (54) = happyShift action_29
action_75 (55) = happyShift action_30
action_75 (56) = happyShift action_31
action_75 (57) = happyShift action_32
action_75 (58) = happyShift action_33
action_75 (60) = happyShift action_34
action_75 (61) = happyShift action_35
action_75 (62) = happyShift action_13
action_75 (15) = happyGoto action_18
action_75 (23) = happyGoto action_92
action_75 (24) = happyGoto action_20
action_75 (25) = happyGoto action_21
action_75 _ = happyFail (happyExpListPerState 75)

action_76 (34) = happyShift action_91
action_76 _ = happyFail (happyExpListPerState 76)

action_77 (28) = happyShift action_23
action_77 (35) = happyShift action_24
action_77 (36) = happyShift action_25
action_77 (43) = happyShift action_26
action_77 (48) = happyShift action_27
action_77 (49) = happyShift action_28
action_77 (54) = happyShift action_29
action_77 (55) = happyShift action_30
action_77 (56) = happyShift action_31
action_77 (57) = happyShift action_32
action_77 (58) = happyShift action_33
action_77 (60) = happyShift action_34
action_77 (61) = happyShift action_35
action_77 (62) = happyShift action_13
action_77 (15) = happyGoto action_18
action_77 (23) = happyGoto action_90
action_77 (24) = happyGoto action_20
action_77 (25) = happyGoto action_21
action_77 _ = happyFail (happyExpListPerState 77)

action_78 (28) = happyShift action_23
action_78 (35) = happyShift action_24
action_78 (36) = happyShift action_25
action_78 (43) = happyShift action_26
action_78 (48) = happyShift action_27
action_78 (49) = happyShift action_28
action_78 (54) = happyShift action_29
action_78 (55) = happyShift action_30
action_78 (56) = happyShift action_31
action_78 (57) = happyShift action_32
action_78 (58) = happyShift action_33
action_78 (60) = happyShift action_34
action_78 (61) = happyShift action_35
action_78 (62) = happyShift action_13
action_78 (15) = happyGoto action_18
action_78 (23) = happyGoto action_89
action_78 (24) = happyGoto action_20
action_78 (25) = happyGoto action_21
action_78 _ = happyFail (happyExpListPerState 78)

action_79 (29) = happyShift action_86
action_79 (30) = happyShift action_87
action_79 (31) = happyShift action_88
action_79 _ = happyFail (happyExpListPerState 79)

action_80 (28) = happyShift action_23
action_80 (35) = happyShift action_24
action_80 (36) = happyShift action_25
action_80 (43) = happyShift action_26
action_80 (48) = happyShift action_27
action_80 (49) = happyShift action_28
action_80 (54) = happyShift action_29
action_80 (55) = happyShift action_30
action_80 (56) = happyShift action_31
action_80 (57) = happyShift action_32
action_80 (58) = happyShift action_33
action_80 (60) = happyShift action_34
action_80 (61) = happyShift action_35
action_80 (62) = happyShift action_13
action_80 (15) = happyGoto action_18
action_80 (23) = happyGoto action_85
action_80 (24) = happyGoto action_20
action_80 (25) = happyGoto action_21
action_80 _ = happyFail (happyExpListPerState 80)

action_81 (28) = happyShift action_23
action_81 (35) = happyShift action_24
action_81 (36) = happyShift action_25
action_81 (43) = happyShift action_26
action_81 (48) = happyShift action_27
action_81 (49) = happyShift action_28
action_81 (54) = happyShift action_29
action_81 (55) = happyShift action_30
action_81 (56) = happyShift action_31
action_81 (57) = happyShift action_32
action_81 (58) = happyShift action_33
action_81 (60) = happyShift action_34
action_81 (61) = happyShift action_35
action_81 (62) = happyShift action_13
action_81 (15) = happyGoto action_18
action_81 (23) = happyGoto action_84
action_81 (24) = happyGoto action_20
action_81 (25) = happyGoto action_21
action_81 _ = happyFail (happyExpListPerState 81)

action_82 (30) = happyShift action_83
action_82 _ = happyFail (happyExpListPerState 82)

action_83 (28) = happyShift action_16
action_83 (37) = happyShift action_17
action_83 (62) = happyShift action_13
action_83 (15) = happyGoto action_14
action_83 (27) = happyGoto action_117
action_83 _ = happyFail (happyExpListPerState 83)

action_84 _ = happyReduce_33

action_85 _ = happyReduce_34

action_86 _ = happyReduce_49

action_87 (28) = happyShift action_23
action_87 (35) = happyShift action_24
action_87 (36) = happyShift action_25
action_87 (43) = happyShift action_26
action_87 (48) = happyShift action_27
action_87 (49) = happyShift action_28
action_87 (54) = happyShift action_29
action_87 (55) = happyShift action_30
action_87 (56) = happyShift action_31
action_87 (57) = happyShift action_32
action_87 (58) = happyShift action_33
action_87 (60) = happyShift action_34
action_87 (61) = happyShift action_35
action_87 (62) = happyShift action_13
action_87 (15) = happyGoto action_18
action_87 (23) = happyGoto action_116
action_87 (24) = happyGoto action_20
action_87 (25) = happyGoto action_21
action_87 _ = happyFail (happyExpListPerState 87)

action_88 (28) = happyShift action_23
action_88 (35) = happyShift action_24
action_88 (36) = happyShift action_25
action_88 (43) = happyShift action_26
action_88 (48) = happyShift action_27
action_88 (49) = happyShift action_28
action_88 (54) = happyShift action_29
action_88 (55) = happyShift action_30
action_88 (56) = happyShift action_31
action_88 (57) = happyShift action_32
action_88 (58) = happyShift action_33
action_88 (60) = happyShift action_34
action_88 (61) = happyShift action_35
action_88 (62) = happyShift action_13
action_88 (15) = happyGoto action_18
action_88 (23) = happyGoto action_115
action_88 (24) = happyGoto action_20
action_88 (25) = happyGoto action_21
action_88 _ = happyFail (happyExpListPerState 88)

action_89 (30) = happyShift action_114
action_89 _ = happyFail (happyExpListPerState 89)

action_90 (30) = happyShift action_113
action_90 _ = happyFail (happyExpListPerState 90)

action_91 (28) = happyShift action_23
action_91 (35) = happyShift action_24
action_91 (36) = happyShift action_25
action_91 (43) = happyShift action_26
action_91 (48) = happyShift action_27
action_91 (49) = happyShift action_28
action_91 (54) = happyShift action_29
action_91 (55) = happyShift action_30
action_91 (56) = happyShift action_31
action_91 (57) = happyShift action_32
action_91 (58) = happyShift action_33
action_91 (60) = happyShift action_34
action_91 (61) = happyShift action_35
action_91 (62) = happyShift action_13
action_91 (15) = happyGoto action_18
action_91 (23) = happyGoto action_112
action_91 (24) = happyGoto action_20
action_91 (25) = happyGoto action_21
action_91 _ = happyFail (happyExpListPerState 91)

action_92 (29) = happyShift action_111
action_92 _ = happyFail (happyExpListPerState 92)

action_93 (31) = happyShift action_110
action_93 _ = happyFail (happyExpListPerState 93)

action_94 (31) = happyShift action_109
action_94 _ = happyFail (happyExpListPerState 94)

action_95 (28) = happyShift action_23
action_95 (35) = happyShift action_24
action_95 (36) = happyShift action_25
action_95 (43) = happyShift action_26
action_95 (48) = happyShift action_27
action_95 (49) = happyShift action_28
action_95 (54) = happyShift action_29
action_95 (55) = happyShift action_30
action_95 (56) = happyShift action_31
action_95 (57) = happyShift action_32
action_95 (58) = happyShift action_33
action_95 (60) = happyShift action_34
action_95 (61) = happyShift action_35
action_95 (62) = happyShift action_13
action_95 (15) = happyGoto action_18
action_95 (23) = happyGoto action_19
action_95 (24) = happyGoto action_20
action_95 (25) = happyGoto action_21
action_95 (26) = happyGoto action_108
action_95 _ = happyFail (happyExpListPerState 95)

action_96 _ = happyReduce_28

action_97 (28) = happyShift action_23
action_97 (35) = happyShift action_24
action_97 (36) = happyShift action_25
action_97 (43) = happyShift action_26
action_97 (48) = happyShift action_27
action_97 (49) = happyShift action_28
action_97 (54) = happyShift action_29
action_97 (55) = happyShift action_30
action_97 (56) = happyShift action_31
action_97 (57) = happyShift action_32
action_97 (58) = happyShift action_33
action_97 (60) = happyShift action_34
action_97 (61) = happyShift action_35
action_97 (62) = happyShift action_13
action_97 (15) = happyGoto action_18
action_97 (23) = happyGoto action_107
action_97 (24) = happyGoto action_20
action_97 (25) = happyGoto action_21
action_97 _ = happyFail (happyExpListPerState 97)

action_98 (28) = happyShift action_23
action_98 (35) = happyShift action_24
action_98 (36) = happyShift action_25
action_98 (43) = happyShift action_26
action_98 (48) = happyShift action_27
action_98 (49) = happyShift action_28
action_98 (54) = happyShift action_29
action_98 (55) = happyShift action_30
action_98 (56) = happyShift action_31
action_98 (57) = happyShift action_32
action_98 (58) = happyShift action_33
action_98 (60) = happyShift action_34
action_98 (61) = happyShift action_35
action_98 (62) = happyShift action_13
action_98 (15) = happyGoto action_18
action_98 (23) = happyGoto action_106
action_98 (24) = happyGoto action_20
action_98 (25) = happyGoto action_21
action_98 _ = happyFail (happyExpListPerState 98)

action_99 (51) = happyShift action_105
action_99 _ = happyFail (happyExpListPerState 99)

action_100 (31) = happyShift action_104
action_100 _ = happyFail (happyExpListPerState 100)

action_101 _ = happyReduce_19

action_102 (41) = happyShift action_50
action_102 (19) = happyGoto action_48
action_102 (20) = happyGoto action_103
action_102 _ = happyReduce_18

action_103 (38) = happyShift action_41
action_103 (39) = happyShift action_42
action_103 (40) = happyShift action_43
action_103 (45) = happyShift action_44
action_103 (46) = happyShift action_45
action_103 (47) = happyShift action_46
action_103 (21) = happyGoto action_39
action_103 (22) = happyGoto action_129
action_103 _ = happyReduce_26

action_104 (28) = happyShift action_23
action_104 (35) = happyShift action_24
action_104 (36) = happyShift action_25
action_104 (43) = happyShift action_26
action_104 (48) = happyShift action_27
action_104 (49) = happyShift action_28
action_104 (54) = happyShift action_29
action_104 (55) = happyShift action_30
action_104 (56) = happyShift action_31
action_104 (57) = happyShift action_32
action_104 (58) = happyShift action_33
action_104 (60) = happyShift action_34
action_104 (61) = happyShift action_35
action_104 (62) = happyShift action_13
action_104 (15) = happyGoto action_18
action_104 (23) = happyGoto action_128
action_104 (24) = happyGoto action_20
action_104 (25) = happyGoto action_21
action_104 _ = happyFail (happyExpListPerState 104)

action_105 (38) = happyShift action_41
action_105 (39) = happyShift action_42
action_105 (40) = happyShift action_43
action_105 (45) = happyShift action_44
action_105 (46) = happyShift action_45
action_105 (47) = happyShift action_46
action_105 (21) = happyGoto action_39
action_105 (22) = happyGoto action_127
action_105 _ = happyReduce_26

action_106 (32) = happyShift action_126
action_106 _ = happyFail (happyExpListPerState 106)

action_107 _ = happyReduce_24

action_108 _ = happyReduce_31

action_109 (28) = happyShift action_23
action_109 (35) = happyShift action_24
action_109 (36) = happyShift action_25
action_109 (43) = happyShift action_26
action_109 (48) = happyShift action_27
action_109 (49) = happyShift action_28
action_109 (54) = happyShift action_29
action_109 (55) = happyShift action_30
action_109 (56) = happyShift action_31
action_109 (57) = happyShift action_32
action_109 (58) = happyShift action_33
action_109 (60) = happyShift action_34
action_109 (61) = happyShift action_35
action_109 (62) = happyShift action_13
action_109 (15) = happyGoto action_18
action_109 (23) = happyGoto action_125
action_109 (24) = happyGoto action_20
action_109 (25) = happyGoto action_21
action_109 _ = happyFail (happyExpListPerState 109)

action_110 (28) = happyShift action_23
action_110 (35) = happyShift action_24
action_110 (36) = happyShift action_25
action_110 (43) = happyShift action_26
action_110 (48) = happyShift action_27
action_110 (49) = happyShift action_28
action_110 (54) = happyShift action_29
action_110 (55) = happyShift action_30
action_110 (56) = happyShift action_31
action_110 (57) = happyShift action_32
action_110 (58) = happyShift action_33
action_110 (60) = happyShift action_34
action_110 (61) = happyShift action_35
action_110 (62) = happyShift action_13
action_110 (15) = happyGoto action_18
action_110 (23) = happyGoto action_124
action_110 (24) = happyGoto action_20
action_110 (25) = happyGoto action_21
action_110 _ = happyFail (happyExpListPerState 110)

action_111 _ = happyReduce_45

action_112 (42) = happyShift action_123
action_112 _ = happyFail (happyExpListPerState 112)

action_113 (28) = happyShift action_23
action_113 (35) = happyShift action_24
action_113 (36) = happyShift action_25
action_113 (43) = happyShift action_26
action_113 (48) = happyShift action_27
action_113 (49) = happyShift action_28
action_113 (54) = happyShift action_29
action_113 (55) = happyShift action_30
action_113 (56) = happyShift action_31
action_113 (57) = happyShift action_32
action_113 (58) = happyShift action_33
action_113 (60) = happyShift action_34
action_113 (61) = happyShift action_35
action_113 (62) = happyShift action_13
action_113 (15) = happyGoto action_18
action_113 (23) = happyGoto action_122
action_113 (24) = happyGoto action_20
action_113 (25) = happyGoto action_21
action_113 _ = happyFail (happyExpListPerState 113)

action_114 (28) = happyShift action_23
action_114 (35) = happyShift action_24
action_114 (36) = happyShift action_25
action_114 (43) = happyShift action_26
action_114 (48) = happyShift action_27
action_114 (49) = happyShift action_28
action_114 (54) = happyShift action_29
action_114 (55) = happyShift action_30
action_114 (56) = happyShift action_31
action_114 (57) = happyShift action_32
action_114 (58) = happyShift action_33
action_114 (60) = happyShift action_34
action_114 (61) = happyShift action_35
action_114 (62) = happyShift action_13
action_114 (15) = happyGoto action_18
action_114 (23) = happyGoto action_121
action_114 (24) = happyGoto action_20
action_114 (25) = happyGoto action_21
action_114 _ = happyFail (happyExpListPerState 114)

action_115 (29) = happyShift action_120
action_115 _ = happyFail (happyExpListPerState 115)

action_116 (29) = happyShift action_119
action_116 _ = happyFail (happyExpListPerState 116)

action_117 (29) = happyShift action_118
action_117 _ = happyFail (happyExpListPerState 117)

action_118 _ = happyReduce_53

action_119 _ = happyReduce_47

action_120 _ = happyReduce_48

action_121 (30) = happyShift action_137
action_121 _ = happyFail (happyExpListPerState 121)

action_122 (30) = happyShift action_136
action_122 _ = happyFail (happyExpListPerState 122)

action_123 (28) = happyShift action_23
action_123 (35) = happyShift action_24
action_123 (36) = happyShift action_25
action_123 (43) = happyShift action_26
action_123 (48) = happyShift action_27
action_123 (49) = happyShift action_28
action_123 (54) = happyShift action_29
action_123 (55) = happyShift action_30
action_123 (56) = happyShift action_31
action_123 (57) = happyShift action_32
action_123 (58) = happyShift action_33
action_123 (60) = happyShift action_34
action_123 (61) = happyShift action_35
action_123 (62) = happyShift action_13
action_123 (15) = happyGoto action_18
action_123 (23) = happyGoto action_19
action_123 (24) = happyGoto action_20
action_123 (25) = happyGoto action_21
action_123 (26) = happyGoto action_135
action_123 _ = happyFail (happyExpListPerState 123)

action_124 (29) = happyShift action_134
action_124 _ = happyFail (happyExpListPerState 124)

action_125 (29) = happyShift action_133
action_125 _ = happyFail (happyExpListPerState 125)

action_126 (28) = happyShift action_23
action_126 (35) = happyShift action_24
action_126 (36) = happyShift action_25
action_126 (43) = happyShift action_26
action_126 (48) = happyShift action_27
action_126 (49) = happyShift action_28
action_126 (54) = happyShift action_29
action_126 (55) = happyShift action_30
action_126 (56) = happyShift action_31
action_126 (57) = happyShift action_32
action_126 (58) = happyShift action_33
action_126 (60) = happyShift action_34
action_126 (61) = happyShift action_35
action_126 (62) = happyShift action_13
action_126 (15) = happyGoto action_18
action_126 (23) = happyGoto action_132
action_126 (24) = happyGoto action_20
action_126 (25) = happyGoto action_21
action_126 _ = happyFail (happyExpListPerState 126)

action_127 (52) = happyShift action_131
action_127 _ = happyFail (happyExpListPerState 127)

action_128 (32) = happyShift action_130
action_128 _ = happyFail (happyExpListPerState 128)

action_129 _ = happyReduce_16

action_130 (28) = happyShift action_23
action_130 (35) = happyShift action_24
action_130 (36) = happyShift action_25
action_130 (43) = happyShift action_26
action_130 (48) = happyShift action_27
action_130 (49) = happyShift action_28
action_130 (54) = happyShift action_29
action_130 (55) = happyShift action_30
action_130 (56) = happyShift action_31
action_130 (57) = happyShift action_32
action_130 (58) = happyShift action_33
action_130 (60) = happyShift action_34
action_130 (61) = happyShift action_35
action_130 (62) = happyShift action_13
action_130 (15) = happyGoto action_18
action_130 (23) = happyGoto action_142
action_130 (24) = happyGoto action_20
action_130 (25) = happyGoto action_21
action_130 _ = happyFail (happyExpListPerState 130)

action_131 _ = happyReduce_22

action_132 _ = happyReduce_20

action_133 (53) = happyShift action_141
action_133 _ = happyFail (happyExpListPerState 133)

action_134 (59) = happyShift action_140
action_134 _ = happyFail (happyExpListPerState 134)

action_135 _ = happyReduce_32

action_136 (28) = happyShift action_23
action_136 (35) = happyShift action_24
action_136 (36) = happyShift action_25
action_136 (43) = happyShift action_26
action_136 (48) = happyShift action_27
action_136 (49) = happyShift action_28
action_136 (54) = happyShift action_29
action_136 (55) = happyShift action_30
action_136 (56) = happyShift action_31
action_136 (57) = happyShift action_32
action_136 (58) = happyShift action_33
action_136 (60) = happyShift action_34
action_136 (61) = happyShift action_35
action_136 (62) = happyShift action_13
action_136 (15) = happyGoto action_18
action_136 (23) = happyGoto action_139
action_136 (24) = happyGoto action_20
action_136 (25) = happyGoto action_21
action_136 _ = happyFail (happyExpListPerState 136)

action_137 (28) = happyShift action_23
action_137 (35) = happyShift action_24
action_137 (36) = happyShift action_25
action_137 (43) = happyShift action_26
action_137 (48) = happyShift action_27
action_137 (49) = happyShift action_28
action_137 (54) = happyShift action_29
action_137 (55) = happyShift action_30
action_137 (56) = happyShift action_31
action_137 (57) = happyShift action_32
action_137 (58) = happyShift action_33
action_137 (60) = happyShift action_34
action_137 (61) = happyShift action_35
action_137 (62) = happyShift action_13
action_137 (15) = happyGoto action_18
action_137 (23) = happyGoto action_138
action_137 (24) = happyGoto action_20
action_137 (25) = happyGoto action_21
action_137 _ = happyFail (happyExpListPerState 137)

action_138 (29) = happyShift action_146
action_138 _ = happyFail (happyExpListPerState 138)

action_139 (29) = happyShift action_145
action_139 _ = happyFail (happyExpListPerState 139)

action_140 (28) = happyShift action_23
action_140 (35) = happyShift action_24
action_140 (36) = happyShift action_25
action_140 (43) = happyShift action_26
action_140 (48) = happyShift action_27
action_140 (49) = happyShift action_28
action_140 (54) = happyShift action_29
action_140 (55) = happyShift action_30
action_140 (56) = happyShift action_31
action_140 (57) = happyShift action_32
action_140 (58) = happyShift action_33
action_140 (60) = happyShift action_34
action_140 (61) = happyShift action_35
action_140 (62) = happyShift action_13
action_140 (15) = happyGoto action_18
action_140 (23) = happyGoto action_19
action_140 (24) = happyGoto action_20
action_140 (25) = happyGoto action_21
action_140 (26) = happyGoto action_144
action_140 _ = happyFail (happyExpListPerState 140)

action_141 (28) = happyShift action_23
action_141 (35) = happyShift action_24
action_141 (36) = happyShift action_25
action_141 (43) = happyShift action_26
action_141 (48) = happyShift action_27
action_141 (49) = happyShift action_28
action_141 (54) = happyShift action_29
action_141 (55) = happyShift action_30
action_141 (56) = happyShift action_31
action_141 (57) = happyShift action_32
action_141 (58) = happyShift action_33
action_141 (60) = happyShift action_34
action_141 (61) = happyShift action_35
action_141 (62) = happyShift action_13
action_141 (15) = happyGoto action_18
action_141 (23) = happyGoto action_19
action_141 (24) = happyGoto action_20
action_141 (25) = happyGoto action_21
action_141 (26) = happyGoto action_143
action_141 _ = happyFail (happyExpListPerState 141)

action_142 _ = happyReduce_21

action_143 _ = happyReduce_30

action_144 _ = happyReduce_29

action_145 _ = happyReduce_46

action_146 _ = happyReduce_44

happyReduce_12 = happySpecReduce_1  15 happyReduction_12
happyReduction_12 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn15
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.VarIdent (tokenText happy_var_1))
	)
happyReduction_12 _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_1  16 happyReduction_13
happyReduction_13 (HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn16
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AProgram (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_13 _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_0  17 happyReduction_14
happyReduction_14  =  HappyAbsSyn17
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_15 = happySpecReduce_2  17 happyReduction_15
happyReduction_15 (HappyAbsSyn17  happy_var_2)
	(HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn17
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_15 _ _  = notHappyAtAll 

happyReduce_16 = happyReduce 5 18 happyReduction_16
happyReduction_16 ((HappyAbsSyn22  happy_var_5) `HappyStk`
	(HappyAbsSyn20  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn18
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AModule (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_5))
	) `HappyStk` happyRest

happyReduce_17 = happySpecReduce_2  19 happyReduction_17
happyReduction_17 (HappyAbsSyn15  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn19
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AnImport (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_17 _ _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_0  20 happyReduction_18
happyReduction_18  =  HappyAbsSyn20
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_19 = happySpecReduce_3  20 happyReduction_19
happyReduction_19 (HappyAbsSyn20  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn20
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_19 _ _ _  = notHappyAtAll 

happyReduce_20 = happyReduce 6 21 happyReduction_20
happyReduction_20 ((HappyAbsSyn23  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn21
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_21 = happyReduce 7 21 happyReduction_21
happyReduction_21 ((HappyAbsSyn23  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn21
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclPrivateDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_22 = happyReduce 6 21 happyReduction_22
happyReduction_22 (_ `HappyStk`
	(HappyAbsSyn22  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn21
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclNamespace (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_5))
	) `HappyStk` happyRest

happyReduce_23 = happySpecReduce_2  21 happyReduction_23
happyReduction_23 (HappyAbsSyn15  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn21
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclOpen (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_23 _ _  = notHappyAtAll 

happyReduce_24 = happyReduce 4 21 happyReduction_24
happyReduction_24 ((HappyAbsSyn23  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn21
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCheck (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_25 = happySpecReduce_2  21 happyReduction_25
happyReduction_25 (HappyAbsSyn23  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn21
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCompute (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_25 _ _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_0  22 happyReduction_26
happyReduction_26  =  HappyAbsSyn22
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_27 = happySpecReduce_1  22 happyReduction_27
happyReduction_27 (HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn22
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_27 _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_3  22 happyReduction_28
happyReduction_28 (HappyAbsSyn22  happy_var_3)
	_
	(HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn22
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_28 _ _ _  = notHappyAtAll 

happyReduce_29 = happyReduce 8 23 happyReduction_29
happyReduction_29 ((HappyAbsSyn26  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pi (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_30 = happyReduce 8 23 happyReduction_30
happyReduction_30 ((HappyAbsSyn26  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Sigma (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_31 = happyReduce 4 23 happyReduction_31
happyReduction_31 ((HappyAbsSyn26  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Lam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_32 = happyReduce 6 23 happyReduction_32
happyReduction_32 ((HappyAbsSyn26  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Let (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_33 = happySpecReduce_3  23 happyReduction_33
happyReduction_33 (HappyAbsSyn23  happy_var_3)
	_
	(HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn23
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Arrow (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_33 _ _ _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_3  23 happyReduction_34
happyReduction_34 (HappyAbsSyn23  happy_var_3)
	_
	(HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn23
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Product (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_34 _ _ _  = notHappyAtAll 

happyReduce_35 = happySpecReduce_1  23 happyReduction_35
happyReduction_35 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn23
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_35 _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_2  24 happyReduction_36
happyReduction_36 (HappyAbsSyn23  happy_var_2)
	(HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn23
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.App (fst happy_var_1) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_36 _ _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_1  24 happyReduction_37
happyReduction_37 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn23
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_37 _  = notHappyAtAll 

happyReduce_38 = happySpecReduce_2  25 happyReduction_38
happyReduction_38 (HappyAbsSyn23  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.First (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_38 _ _  = notHappyAtAll 

happyReduce_39 = happySpecReduce_2  25 happyReduction_39
happyReduction_39 (HappyAbsSyn23  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Second (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_39 _ _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_1  25 happyReduction_40
happyReduction_40 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Universe (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_40 _  = notHappyAtAll 

happyReduce_41 = happySpecReduce_1  25 happyReduction_41
happyReduction_41 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_41 _  = notHappyAtAll 

happyReduce_42 = happySpecReduce_1  25 happyReduction_42
happyReduction_42 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitVal (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_42 _  = notHappyAtAll 

happyReduce_43 = happySpecReduce_1  25 happyReduction_43
happyReduction_43 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn23
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Var (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_43 _  = notHappyAtAll 

happyReduce_44 = happyReduce 8 25 happyReduction_44
happyReduction_44 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.IdType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_45 = happyReduce 4 25 happyReduction_45
happyReduction_45 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Refl (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_46 = happyReduce 8 25 happyReduction_46
happyReduction_46 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.J (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_47 = happyReduce 5 25 happyReduction_47
happyReduction_47 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_48 = happyReduce 5 25 happyReduction_48
happyReduction_48 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Ann (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_49 = happySpecReduce_3  25 happyReduction_49
happyReduction_49 _
	(HappyAbsSyn23  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), (snd happy_var_2))
	)
happyReduction_49 _ _ _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_1  26 happyReduction_50
happyReduction_50 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn26
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AScopedTerm (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_50 _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_1  27 happyReduction_51
happyReduction_51 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn27
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternWildcard (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_51 _  = notHappyAtAll 

happyReduce_52 = happySpecReduce_1  27 happyReduction_52
happyReduction_52 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn27
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.PatternVar (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_52 _  = notHappyAtAll 

happyReduce_53 = happyReduce 5 27 happyReduction_53
happyReduction_53 (_ `HappyStk`
	(HappyAbsSyn27  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn27
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternPair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyNewToken action sts stk [] =
	action 63 63 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 28;
	PT _ (TS _ 2) -> cont 29;
	PT _ (TS _ 3) -> cont 30;
	PT _ (TS _ 4) -> cont 31;
	PT _ (TS _ 5) -> cont 32;
	PT _ (TS _ 6) -> cont 33;
	PT _ (TS _ 7) -> cont 34;
	PT _ (TS _ 8) -> cont 35;
	PT _ (TS _ 9) -> cont 36;
	PT _ (TS _ 10) -> cont 37;
	PT _ (TS _ 11) -> cont 38;
	PT _ (TS _ 12) -> cont 39;
	PT _ (TS _ 13) -> cont 40;
	PT _ (TS _ 14) -> cont 41;
	PT _ (TS _ 15) -> cont 42;
	PT _ (TS _ 16) -> cont 43;
	PT _ (TS _ 17) -> cont 44;
	PT _ (TS _ 18) -> cont 45;
	PT _ (TS _ 19) -> cont 46;
	PT _ (TS _ 20) -> cont 47;
	PT _ (TS _ 21) -> cont 48;
	PT _ (TS _ 22) -> cont 49;
	PT _ (TS _ 23) -> cont 50;
	PT _ (TS _ 24) -> cont 51;
	PT _ (TS _ 25) -> cont 52;
	PT _ (TS _ 26) -> cont 53;
	PT _ (TS _ 27) -> cont 54;
	PT _ (TS _ 28) -> cont 55;
	PT _ (TS _ 29) -> cont 56;
	PT _ (TS _ 30) -> cont 57;
	PT _ (TS _ 31) -> cont 58;
	PT _ (TS _ 32) -> cont 59;
	PT _ (TS _ 33) -> cont 60;
	PT _ (TS _ 34) -> cont 61;
	PT _ (T_VarIdent _) -> cont 62;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 63 tk tks = happyError' (tks, explist)
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
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn16 z -> happyReturn z; _other -> notHappyAtAll })

pListModule_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn17 z -> happyReturn z; _other -> notHappyAtAll })

pModule_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_2 tks) (\x -> case x of {HappyAbsSyn18 z -> happyReturn z; _other -> notHappyAtAll })

pImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_3 tks) (\x -> case x of {HappyAbsSyn19 z -> happyReturn z; _other -> notHappyAtAll })

pListImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_4 tks) (\x -> case x of {HappyAbsSyn20 z -> happyReturn z; _other -> notHappyAtAll })

pDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_5 tks) (\x -> case x of {HappyAbsSyn21 z -> happyReturn z; _other -> notHappyAtAll })

pListDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_6 tks) (\x -> case x of {HappyAbsSyn22 z -> happyReturn z; _other -> notHappyAtAll })

pTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_7 tks) (\x -> case x of {HappyAbsSyn23 z -> happyReturn z; _other -> notHappyAtAll })

pTerm1_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_8 tks) (\x -> case x of {HappyAbsSyn23 z -> happyReturn z; _other -> notHappyAtAll })

pTerm2_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_9 tks) (\x -> case x of {HappyAbsSyn23 z -> happyReturn z; _other -> notHappyAtAll })

pScopedTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_10 tks) (\x -> case x of {HappyAbsSyn26 z -> happyReturn z; _other -> notHappyAtAll })

pPattern_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_11 tks) (\x -> case x of {HappyAbsSyn27 z -> happyReturn z; _other -> notHappyAtAll })

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

pListModule :: [Token] -> Err [Language.MLTT.Syntax.Abs.Module]
pListModule = fmap snd . pListModule_internal

pModule :: [Token] -> Err Language.MLTT.Syntax.Abs.Module
pModule = fmap snd . pModule_internal

pImport :: [Token] -> Err Language.MLTT.Syntax.Abs.Import
pImport = fmap snd . pImport_internal

pListImport :: [Token] -> Err [Language.MLTT.Syntax.Abs.Import]
pListImport = fmap snd . pListImport_internal

pDecl :: [Token] -> Err Language.MLTT.Syntax.Abs.Decl
pDecl = fmap snd . pDecl_internal

pListDecl :: [Token] -> Err [Language.MLTT.Syntax.Abs.Decl]
pListDecl = fmap snd . pListDecl_internal

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
