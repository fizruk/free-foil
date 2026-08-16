{-# OPTIONS_GHC -w #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.MLTT.Syntax.Par
  ( happyError
  , myLexer
  , pProgram
  , pListUnit
  , pUnit
  , pModule
  , pInclude
  , pListInclude
  , pRefinement
  , pFixed
  , pListFixed
  , pTelescopeDecl
  , pParam
  , pListParam
  , pImport
  , pListImport
  , pDecl
  , pListDecl
  , pDischarge
  , pListVarIdent
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
	| HappyAbsSyn26 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.VarIdent))
	| HappyAbsSyn27 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Program))
	| HappyAbsSyn28 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Unit]))
	| HappyAbsSyn29 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Unit))
	| HappyAbsSyn30 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Module))
	| HappyAbsSyn31 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Include))
	| HappyAbsSyn32 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Include]))
	| HappyAbsSyn33 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Refinement))
	| HappyAbsSyn34 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Fixed))
	| HappyAbsSyn35 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Fixed]))
	| HappyAbsSyn36 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.TelescopeDecl))
	| HappyAbsSyn37 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Param))
	| HappyAbsSyn38 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Param]))
	| HappyAbsSyn39 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Import))
	| HappyAbsSyn40 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Import]))
	| HappyAbsSyn41 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Decl))
	| HappyAbsSyn42 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Decl]))
	| HappyAbsSyn43 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Discharge))
	| HappyAbsSyn44 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.VarIdent]))
	| HappyAbsSyn45 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Term))
	| HappyAbsSyn48 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.ScopedTerm))
	| HappyAbsSyn49 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Pattern))

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
 action_146,
 action_147,
 action_148,
 action_149,
 action_150,
 action_151,
 action_152,
 action_153,
 action_154,
 action_155,
 action_156,
 action_157,
 action_158,
 action_159,
 action_160,
 action_161,
 action_162,
 action_163,
 action_164,
 action_165,
 action_166,
 action_167,
 action_168,
 action_169,
 action_170,
 action_171,
 action_172,
 action_173,
 action_174,
 action_175,
 action_176,
 action_177,
 action_178,
 action_179,
 action_180,
 action_181,
 action_182,
 action_183,
 action_184,
 action_185,
 action_186,
 action_187,
 action_188,
 action_189,
 action_190,
 action_191,
 action_192,
 action_193,
 action_194,
 action_195,
 action_196,
 action_197,
 action_198,
 action_199,
 action_200,
 action_201,
 action_202,
 action_203,
 action_204,
 action_205,
 action_206,
 action_207,
 action_208,
 action_209,
 action_210,
 action_211 :: () => Prelude.Int -> ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

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
 happyReduce_53,
 happyReduce_54,
 happyReduce_55,
 happyReduce_56,
 happyReduce_57,
 happyReduce_58,
 happyReduce_59,
 happyReduce_60,
 happyReduce_61,
 happyReduce_62,
 happyReduce_63,
 happyReduce_64,
 happyReduce_65,
 happyReduce_66,
 happyReduce_67,
 happyReduce_68,
 happyReduce_69,
 happyReduce_70,
 happyReduce_71,
 happyReduce_72,
 happyReduce_73,
 happyReduce_74,
 happyReduce_75,
 happyReduce_76,
 happyReduce_77,
 happyReduce_78,
 happyReduce_79,
 happyReduce_80,
 happyReduce_81,
 happyReduce_82,
 happyReduce_83,
 happyReduce_84,
 happyReduce_85 :: () => ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,432) ([0,0,0,0,520,0,0,0,0,8192,8,0,0,0,0,8320,0,0,0,0,0,2,0,0,0,0,512,0,0,0,0,0,8,0,0,0,0,1,0,0,0,0,0,0,16384,0,0,0,0,0,256,0,0,0,0,8,0,0,0,32,0,0,0,0,32768,0,0,0,0,0,0,128,0,0,0,0,0,2,0,0,0,0,1792,11,0,0,0,0,11292,0,0,0,0,0,64,0,0,0,0,0,0,4,0,0,24608,20544,7416,0,0,32768,384,320,115,0,0,512,6,52229,1,0,0,6152,5136,1854,0,0,8192,128,0,16,0,0,0,0,16384,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32768,512,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32896,16385,30481,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24608,20544,7416,0,0,32768,0,0,0,0,0,512,0,0,0,0,0,8200,0,1024,0,0,8192,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,2048,0,0,0,0,0,32800,0,4096,0,0,32768,384,320,115,0,0,512,6,52229,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1538,1280,460,0,0,0,0,0,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,1538,34052,463,0,0,2048,4120,15892,7,0,0,0,0,4096,0,0,0,0,0,64,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,8192,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,32768,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,256,0,0,0,1,0,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,256,0,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8192,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,256,0,0,0,0,0,4,0,0,24608,20544,7416,0,0,0,32768,0,0,0,0,8192,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,256,0,0,0,0,0,0,0,0,0,32768,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,128,0,0,0,0,0,1792,11,0,0,0,0,0,16384,0,0,0,0,0,256,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8192,0,0,0,8200,0,1024,0,0,8192,128,0,16,0,0,32896,16641,29665,0,0,0,256,0,0,0,0,2048,4120,15892,7,0,0,24608,20544,7416,0,0,0,11,0,0,0,0,512,1030,53125,1,0,0,6152,5136,1854,0,0,32768,0,0,0,0,0,128,2,16384,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32768,384,57665,115,0,0,512,1030,53125,1,0,0,32,0,0,0,0,32768,0,0,0,0,0,32896,16641,29665,0,0,0,4,0,0,0,0,32768,0,0,0,0,0,512,0,0,0,0,32768,384,57665,115,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,32896,16641,29665,0,0,0,32,0,0,0,0,0,0,64,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,512,1030,53125,1,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8192,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,512,0,0,0,0,16384,4,0,0,0,0,2048,0,0,0,0,0,28672,176,0,0,0,2048,4120,15892,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6152,5136,1854,0,0,8192,16480,63568,28,0,0,0,0,0,0,0,0,0,1,0,0,0,2048,4120,15892,7,0,0,24608,20544,7416,0,0,0,1,0,0,0,0,1024,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8192,0,0,0,0,0,128,0,0,0,0,32768,384,57665,115,0,0,1024,0,0,0,0,0,16,0,0,0,0,0,4,0,0,0,0,0,0,8,0,0,0,1538,34052,463,0,0,0,0,0,0,0,0,24608,20544,7416,0,0,0,0,0,0,0,0,0,128,0,0,0,0,49152,705,0,0,0,16384,0,0,0,0,0,4096,0,0,0,0,0,0,0,0,0,0,2048,4120,15892,7,0,0,0,0,4,0,0,0,0,0,4,0,0,0,0,0,0,0,0,6152,5136,1854,0,0,8192,16480,63568,28,0,0,256,0,0,0,0,0,4,0,0,0,0,2048,4120,15892,7,0,0,24608,20544,7416,0,0,0,0,0,0,0,0,512,1030,53125,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram_internal","%start_pListUnit_internal","%start_pUnit_internal","%start_pModule_internal","%start_pInclude_internal","%start_pListInclude_internal","%start_pRefinement_internal","%start_pFixed_internal","%start_pListFixed_internal","%start_pTelescopeDecl_internal","%start_pParam_internal","%start_pListParam_internal","%start_pImport_internal","%start_pListImport_internal","%start_pDecl_internal","%start_pListDecl_internal","%start_pDischarge_internal","%start_pListVarIdent_internal","%start_pTerm_internal","%start_pTerm1_internal","%start_pTerm2_internal","%start_pScopedTerm_internal","%start_pPattern_internal","VarIdent","Program","ListUnit","Unit","Module","Include","ListInclude","Refinement","Fixed","ListFixed","TelescopeDecl","Param","ListParam","Import","ListImport","Decl","ListDecl","Discharge","ListVarIdent","Term","Term1","Term2","ScopedTerm","Pattern","'('","')'","','","'/'","':'","':='","';'","'='","'Id'","'J'","'_'","'check'","'compute'","'def'","'import'","'in'","'include'","'let'","'module'","'namespace'","'open'","'over'","'private'","'refl'","'telescope'","'tt'","'where'","'{'","'}'","'\215'","'\928'","'\931'","'\955'","'\960\8321'","'\960\8322'","'\8594'","'\8658'","'\120140'","'\120793'","L_VarIdent","%eof"]
        bit_start = st Prelude.* 90
        bit_end = (st Prelude.+ 1) Prelude.* 90
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..89]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (68) = happyShift action_84
action_0 (74) = happyShift action_72
action_0 (27) = happyGoto action_90
action_0 (28) = happyGoto action_91
action_0 (29) = happyGoto action_89
action_0 (30) = happyGoto action_86
action_0 (36) = happyGoto action_87
action_0 _ = happyReduce_25

action_1 (68) = happyShift action_84
action_1 (74) = happyShift action_72
action_1 (28) = happyGoto action_88
action_1 (29) = happyGoto action_89
action_1 (30) = happyGoto action_86
action_1 (36) = happyGoto action_87
action_1 _ = happyReduce_25

action_2 (68) = happyShift action_84
action_2 (74) = happyShift action_72
action_2 (29) = happyGoto action_85
action_2 (30) = happyGoto action_86
action_2 (36) = happyGoto action_87
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (68) = happyShift action_84
action_3 (30) = happyGoto action_83
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (66) = happyShift action_81
action_4 (31) = happyGoto action_82
action_4 _ = happyFail (happyExpListPerState 4)

action_5 (66) = happyShift action_81
action_5 (31) = happyGoto action_79
action_5 (32) = happyGoto action_80
action_5 _ = happyReduce_31

action_6 (53) = happyShift action_78
action_6 (33) = happyGoto action_77
action_6 _ = happyReduce_33

action_7 (89) = happyShift action_24
action_7 (26) = happyGoto action_73
action_7 (34) = happyGoto action_76
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (89) = happyShift action_24
action_8 (26) = happyGoto action_73
action_8 (34) = happyGoto action_74
action_8 (35) = happyGoto action_75
action_8 _ = happyReduce_36

action_9 (74) = happyShift action_72
action_9 (36) = happyGoto action_71
action_9 _ = happyFail (happyExpListPerState 9)

action_10 (50) = happyShift action_69
action_10 (37) = happyGoto action_70
action_10 _ = happyFail (happyExpListPerState 10)

action_11 (50) = happyShift action_69
action_11 (37) = happyGoto action_67
action_11 (38) = happyGoto action_68
action_11 _ = happyReduce_42

action_12 (64) = happyShift action_65
action_12 (39) = happyGoto action_66
action_12 _ = happyFail (happyExpListPerState 12)

action_13 (64) = happyShift action_65
action_13 (39) = happyGoto action_63
action_13 (40) = happyGoto action_64
action_13 _ = happyReduce_45

action_14 (61) = happyShift action_56
action_14 (62) = happyShift action_57
action_14 (63) = happyShift action_58
action_14 (69) = happyShift action_59
action_14 (70) = happyShift action_60
action_14 (72) = happyShift action_61
action_14 (41) = happyGoto action_62
action_14 _ = happyFail (happyExpListPerState 14)

action_15 (61) = happyShift action_56
action_15 (62) = happyShift action_57
action_15 (63) = happyShift action_58
action_15 (69) = happyShift action_59
action_15 (70) = happyShift action_60
action_15 (72) = happyShift action_61
action_15 (41) = happyGoto action_54
action_15 (42) = happyGoto action_55
action_15 _ = happyReduce_53

action_16 (71) = happyShift action_53
action_16 (43) = happyGoto action_52
action_16 _ = happyReduce_56

action_17 (89) = happyShift action_24
action_17 (26) = happyGoto action_50
action_17 (44) = happyGoto action_51
action_17 _ = happyReduce_58

action_18 (50) = happyShift action_34
action_18 (58) = happyShift action_35
action_18 (59) = happyShift action_36
action_18 (67) = happyShift action_37
action_18 (73) = happyShift action_38
action_18 (75) = happyShift action_39
action_18 (80) = happyShift action_40
action_18 (81) = happyShift action_41
action_18 (82) = happyShift action_42
action_18 (83) = happyShift action_43
action_18 (84) = happyShift action_44
action_18 (87) = happyShift action_45
action_18 (88) = happyShift action_46
action_18 (89) = happyShift action_24
action_18 (26) = happyGoto action_29
action_18 (45) = happyGoto action_49
action_18 (46) = happyGoto action_31
action_18 (47) = happyGoto action_32
action_18 _ = happyFail (happyExpListPerState 18)

action_19 (50) = happyShift action_34
action_19 (58) = happyShift action_35
action_19 (59) = happyShift action_36
action_19 (73) = happyShift action_38
action_19 (75) = happyShift action_39
action_19 (83) = happyShift action_43
action_19 (84) = happyShift action_44
action_19 (87) = happyShift action_45
action_19 (88) = happyShift action_46
action_19 (89) = happyShift action_24
action_19 (26) = happyGoto action_29
action_19 (46) = happyGoto action_48
action_19 (47) = happyGoto action_32
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (50) = happyShift action_34
action_20 (58) = happyShift action_35
action_20 (59) = happyShift action_36
action_20 (73) = happyShift action_38
action_20 (75) = happyShift action_39
action_20 (83) = happyShift action_43
action_20 (84) = happyShift action_44
action_20 (87) = happyShift action_45
action_20 (88) = happyShift action_46
action_20 (89) = happyShift action_24
action_20 (26) = happyGoto action_29
action_20 (47) = happyGoto action_47
action_20 _ = happyFail (happyExpListPerState 20)

action_21 (50) = happyShift action_34
action_21 (58) = happyShift action_35
action_21 (59) = happyShift action_36
action_21 (67) = happyShift action_37
action_21 (73) = happyShift action_38
action_21 (75) = happyShift action_39
action_21 (80) = happyShift action_40
action_21 (81) = happyShift action_41
action_21 (82) = happyShift action_42
action_21 (83) = happyShift action_43
action_21 (84) = happyShift action_44
action_21 (87) = happyShift action_45
action_21 (88) = happyShift action_46
action_21 (89) = happyShift action_24
action_21 (26) = happyGoto action_29
action_21 (45) = happyGoto action_30
action_21 (46) = happyGoto action_31
action_21 (47) = happyGoto action_32
action_21 (48) = happyGoto action_33
action_21 _ = happyFail (happyExpListPerState 21)

action_22 (50) = happyShift action_27
action_22 (60) = happyShift action_28
action_22 (89) = happyShift action_24
action_22 (26) = happyGoto action_25
action_22 (49) = happyGoto action_26
action_22 _ = happyFail (happyExpListPerState 22)

action_23 (89) = happyShift action_24
action_23 _ = happyFail (happyExpListPerState 23)

action_24 _ = happyReduce_23

action_25 _ = happyReduce_84

action_26 (90) = happyAccept
action_26 _ = happyFail (happyExpListPerState 26)

action_27 (50) = happyShift action_27
action_27 (60) = happyShift action_28
action_27 (89) = happyShift action_24
action_27 (26) = happyGoto action_25
action_27 (49) = happyGoto action_126
action_27 _ = happyFail (happyExpListPerState 27)

action_28 _ = happyReduce_83

action_29 _ = happyReduce_75

action_30 _ = happyReduce_82

action_31 (50) = happyShift action_34
action_31 (58) = happyShift action_35
action_31 (59) = happyShift action_36
action_31 (73) = happyShift action_38
action_31 (75) = happyShift action_39
action_31 (79) = happyShift action_124
action_31 (83) = happyShift action_43
action_31 (84) = happyShift action_44
action_31 (85) = happyShift action_125
action_31 (87) = happyShift action_45
action_31 (88) = happyShift action_46
action_31 (89) = happyShift action_24
action_31 (26) = happyGoto action_29
action_31 (47) = happyGoto action_113
action_31 _ = happyReduce_67

action_32 _ = happyReduce_69

action_33 (90) = happyAccept
action_33 _ = happyFail (happyExpListPerState 33)

action_34 (50) = happyShift action_34
action_34 (58) = happyShift action_35
action_34 (59) = happyShift action_36
action_34 (67) = happyShift action_37
action_34 (73) = happyShift action_38
action_34 (75) = happyShift action_39
action_34 (80) = happyShift action_40
action_34 (81) = happyShift action_41
action_34 (82) = happyShift action_42
action_34 (83) = happyShift action_43
action_34 (84) = happyShift action_44
action_34 (87) = happyShift action_45
action_34 (88) = happyShift action_46
action_34 (89) = happyShift action_24
action_34 (26) = happyGoto action_29
action_34 (45) = happyGoto action_123
action_34 (46) = happyGoto action_31
action_34 (47) = happyGoto action_32
action_34 _ = happyFail (happyExpListPerState 34)

action_35 (50) = happyShift action_122
action_35 _ = happyFail (happyExpListPerState 35)

action_36 (50) = happyShift action_121
action_36 _ = happyFail (happyExpListPerState 36)

action_37 (50) = happyShift action_27
action_37 (60) = happyShift action_28
action_37 (89) = happyShift action_24
action_37 (26) = happyGoto action_25
action_37 (49) = happyGoto action_120
action_37 _ = happyFail (happyExpListPerState 37)

action_38 (50) = happyShift action_119
action_38 _ = happyFail (happyExpListPerState 38)

action_39 _ = happyReduce_74

action_40 (50) = happyShift action_118
action_40 _ = happyFail (happyExpListPerState 40)

action_41 (50) = happyShift action_117
action_41 _ = happyFail (happyExpListPerState 41)

action_42 (50) = happyShift action_27
action_42 (60) = happyShift action_28
action_42 (89) = happyShift action_24
action_42 (26) = happyGoto action_25
action_42 (49) = happyGoto action_116
action_42 _ = happyFail (happyExpListPerState 42)

action_43 (50) = happyShift action_34
action_43 (58) = happyShift action_35
action_43 (59) = happyShift action_36
action_43 (73) = happyShift action_38
action_43 (75) = happyShift action_39
action_43 (83) = happyShift action_43
action_43 (84) = happyShift action_44
action_43 (87) = happyShift action_45
action_43 (88) = happyShift action_46
action_43 (89) = happyShift action_24
action_43 (26) = happyGoto action_29
action_43 (47) = happyGoto action_115
action_43 _ = happyFail (happyExpListPerState 43)

action_44 (50) = happyShift action_34
action_44 (58) = happyShift action_35
action_44 (59) = happyShift action_36
action_44 (73) = happyShift action_38
action_44 (75) = happyShift action_39
action_44 (83) = happyShift action_43
action_44 (84) = happyShift action_44
action_44 (87) = happyShift action_45
action_44 (88) = happyShift action_46
action_44 (89) = happyShift action_24
action_44 (26) = happyGoto action_29
action_44 (47) = happyGoto action_114
action_44 _ = happyFail (happyExpListPerState 44)

action_45 _ = happyReduce_72

action_46 _ = happyReduce_73

action_47 (90) = happyAccept
action_47 _ = happyFail (happyExpListPerState 47)

action_48 (50) = happyShift action_34
action_48 (58) = happyShift action_35
action_48 (59) = happyShift action_36
action_48 (73) = happyShift action_38
action_48 (75) = happyShift action_39
action_48 (83) = happyShift action_43
action_48 (84) = happyShift action_44
action_48 (87) = happyShift action_45
action_48 (88) = happyShift action_46
action_48 (89) = happyShift action_24
action_48 (90) = happyAccept
action_48 (26) = happyGoto action_29
action_48 (47) = happyGoto action_113
action_48 _ = happyFail (happyExpListPerState 48)

action_49 (90) = happyAccept
action_49 _ = happyFail (happyExpListPerState 49)

action_50 (52) = happyShift action_112
action_50 _ = happyReduce_59

action_51 (90) = happyAccept
action_51 _ = happyFail (happyExpListPerState 51)

action_52 (90) = happyAccept
action_52 _ = happyFail (happyExpListPerState 52)

action_53 (50) = happyShift action_111
action_53 _ = happyFail (happyExpListPerState 53)

action_54 (56) = happyShift action_110
action_54 _ = happyReduce_54

action_55 (90) = happyAccept
action_55 _ = happyFail (happyExpListPerState 55)

action_56 (50) = happyShift action_34
action_56 (58) = happyShift action_35
action_56 (59) = happyShift action_36
action_56 (67) = happyShift action_37
action_56 (73) = happyShift action_38
action_56 (75) = happyShift action_39
action_56 (80) = happyShift action_40
action_56 (81) = happyShift action_41
action_56 (82) = happyShift action_42
action_56 (83) = happyShift action_43
action_56 (84) = happyShift action_44
action_56 (87) = happyShift action_45
action_56 (88) = happyShift action_46
action_56 (89) = happyShift action_24
action_56 (26) = happyGoto action_29
action_56 (45) = happyGoto action_109
action_56 (46) = happyGoto action_31
action_56 (47) = happyGoto action_32
action_56 _ = happyFail (happyExpListPerState 56)

action_57 (50) = happyShift action_34
action_57 (58) = happyShift action_35
action_57 (59) = happyShift action_36
action_57 (67) = happyShift action_37
action_57 (73) = happyShift action_38
action_57 (75) = happyShift action_39
action_57 (80) = happyShift action_40
action_57 (81) = happyShift action_41
action_57 (82) = happyShift action_42
action_57 (83) = happyShift action_43
action_57 (84) = happyShift action_44
action_57 (87) = happyShift action_45
action_57 (88) = happyShift action_46
action_57 (89) = happyShift action_24
action_57 (26) = happyGoto action_29
action_57 (45) = happyGoto action_108
action_57 (46) = happyGoto action_31
action_57 (47) = happyGoto action_32
action_57 _ = happyFail (happyExpListPerState 57)

action_58 (89) = happyShift action_24
action_58 (26) = happyGoto action_107
action_58 _ = happyFail (happyExpListPerState 58)

action_59 (89) = happyShift action_24
action_59 (26) = happyGoto action_106
action_59 _ = happyFail (happyExpListPerState 59)

action_60 (89) = happyShift action_24
action_60 (26) = happyGoto action_105
action_60 _ = happyFail (happyExpListPerState 60)

action_61 (63) = happyShift action_104
action_61 _ = happyFail (happyExpListPerState 61)

action_62 (90) = happyAccept
action_62 _ = happyFail (happyExpListPerState 62)

action_63 (56) = happyShift action_103
action_63 _ = happyFail (happyExpListPerState 63)

action_64 (90) = happyAccept
action_64 _ = happyFail (happyExpListPerState 64)

action_65 (89) = happyShift action_24
action_65 (26) = happyGoto action_102
action_65 _ = happyFail (happyExpListPerState 65)

action_66 (90) = happyAccept
action_66 _ = happyFail (happyExpListPerState 66)

action_67 (50) = happyShift action_69
action_67 (37) = happyGoto action_67
action_67 (38) = happyGoto action_101
action_67 _ = happyReduce_42

action_68 (90) = happyAccept
action_68 _ = happyFail (happyExpListPerState 68)

action_69 (89) = happyShift action_24
action_69 (26) = happyGoto action_100
action_69 _ = happyFail (happyExpListPerState 69)

action_70 (90) = happyAccept
action_70 _ = happyFail (happyExpListPerState 70)

action_71 (90) = happyAccept
action_71 _ = happyFail (happyExpListPerState 71)

action_72 (89) = happyShift action_24
action_72 (26) = happyGoto action_99
action_72 _ = happyFail (happyExpListPerState 72)

action_73 (55) = happyShift action_98
action_73 _ = happyFail (happyExpListPerState 73)

action_74 (52) = happyShift action_97
action_74 _ = happyReduce_37

action_75 (90) = happyAccept
action_75 _ = happyFail (happyExpListPerState 75)

action_76 (90) = happyAccept
action_76 _ = happyFail (happyExpListPerState 76)

action_77 (90) = happyAccept
action_77 _ = happyFail (happyExpListPerState 77)

action_78 (77) = happyShift action_96
action_78 _ = happyFail (happyExpListPerState 78)

action_79 (66) = happyShift action_81
action_79 (31) = happyGoto action_79
action_79 (32) = happyGoto action_95
action_79 _ = happyReduce_31

action_80 (90) = happyAccept
action_80 _ = happyFail (happyExpListPerState 80)

action_81 (89) = happyShift action_24
action_81 (26) = happyGoto action_94
action_81 _ = happyFail (happyExpListPerState 81)

action_82 (90) = happyAccept
action_82 _ = happyFail (happyExpListPerState 82)

action_83 (90) = happyAccept
action_83 _ = happyFail (happyExpListPerState 83)

action_84 (89) = happyShift action_24
action_84 (26) = happyGoto action_93
action_84 _ = happyFail (happyExpListPerState 84)

action_85 (90) = happyAccept
action_85 _ = happyFail (happyExpListPerState 85)

action_86 _ = happyReduce_27

action_87 _ = happyReduce_28

action_88 (90) = happyAccept
action_88 _ = happyFail (happyExpListPerState 88)

action_89 (68) = happyShift action_84
action_89 (74) = happyShift action_72
action_89 (28) = happyGoto action_92
action_89 (29) = happyGoto action_89
action_89 (30) = happyGoto action_86
action_89 (36) = happyGoto action_87
action_89 _ = happyReduce_25

action_90 (90) = happyAccept
action_90 _ = happyFail (happyExpListPerState 90)

action_91 _ = happyReduce_24

action_92 _ = happyReduce_26

action_93 (66) = happyShift action_81
action_93 (31) = happyGoto action_79
action_93 (32) = happyGoto action_154
action_93 _ = happyReduce_31

action_94 (53) = happyShift action_78
action_94 (33) = happyGoto action_153
action_94 _ = happyReduce_33

action_95 _ = happyReduce_32

action_96 (89) = happyShift action_24
action_96 (26) = happyGoto action_73
action_96 (34) = happyGoto action_74
action_96 (35) = happyGoto action_152
action_96 _ = happyReduce_36

action_97 (89) = happyShift action_24
action_97 (26) = happyGoto action_73
action_97 (34) = happyGoto action_74
action_97 (35) = happyGoto action_151
action_97 _ = happyReduce_36

action_98 (50) = happyShift action_34
action_98 (58) = happyShift action_35
action_98 (59) = happyShift action_36
action_98 (67) = happyShift action_37
action_98 (73) = happyShift action_38
action_98 (75) = happyShift action_39
action_98 (80) = happyShift action_40
action_98 (81) = happyShift action_41
action_98 (82) = happyShift action_42
action_98 (83) = happyShift action_43
action_98 (84) = happyShift action_44
action_98 (87) = happyShift action_45
action_98 (88) = happyShift action_46
action_98 (89) = happyShift action_24
action_98 (26) = happyGoto action_29
action_98 (45) = happyGoto action_150
action_98 (46) = happyGoto action_31
action_98 (47) = happyGoto action_32
action_98 _ = happyFail (happyExpListPerState 98)

action_99 (66) = happyShift action_81
action_99 (31) = happyGoto action_79
action_99 (32) = happyGoto action_149
action_99 _ = happyReduce_31

action_100 (54) = happyShift action_148
action_100 _ = happyFail (happyExpListPerState 100)

action_101 _ = happyReduce_43

action_102 _ = happyReduce_44

action_103 (64) = happyShift action_65
action_103 (39) = happyGoto action_63
action_103 (40) = happyGoto action_147
action_103 _ = happyReduce_45

action_104 (89) = happyShift action_24
action_104 (26) = happyGoto action_146
action_104 _ = happyFail (happyExpListPerState 104)

action_105 _ = happyReduce_50

action_106 (76) = happyShift action_145
action_106 _ = happyFail (happyExpListPerState 106)

action_107 (71) = happyShift action_53
action_107 (43) = happyGoto action_144
action_107 _ = happyReduce_56

action_108 _ = happyReduce_52

action_109 (54) = happyShift action_143
action_109 _ = happyFail (happyExpListPerState 109)

action_110 (61) = happyShift action_56
action_110 (62) = happyShift action_57
action_110 (63) = happyShift action_58
action_110 (69) = happyShift action_59
action_110 (70) = happyShift action_60
action_110 (72) = happyShift action_61
action_110 (41) = happyGoto action_54
action_110 (42) = happyGoto action_142
action_110 _ = happyReduce_53

action_111 (89) = happyShift action_24
action_111 (26) = happyGoto action_50
action_111 (44) = happyGoto action_141
action_111 _ = happyReduce_58

action_112 (89) = happyShift action_24
action_112 (26) = happyGoto action_50
action_112 (44) = happyGoto action_140
action_112 _ = happyReduce_58

action_113 _ = happyReduce_68

action_114 _ = happyReduce_71

action_115 _ = happyReduce_70

action_116 (86) = happyShift action_139
action_116 _ = happyFail (happyExpListPerState 116)

action_117 (50) = happyShift action_27
action_117 (60) = happyShift action_28
action_117 (89) = happyShift action_24
action_117 (26) = happyGoto action_25
action_117 (49) = happyGoto action_138
action_117 _ = happyFail (happyExpListPerState 117)

action_118 (50) = happyShift action_27
action_118 (60) = happyShift action_28
action_118 (89) = happyShift action_24
action_118 (26) = happyGoto action_25
action_118 (49) = happyGoto action_137
action_118 _ = happyFail (happyExpListPerState 118)

action_119 (50) = happyShift action_34
action_119 (58) = happyShift action_35
action_119 (59) = happyShift action_36
action_119 (67) = happyShift action_37
action_119 (73) = happyShift action_38
action_119 (75) = happyShift action_39
action_119 (80) = happyShift action_40
action_119 (81) = happyShift action_41
action_119 (82) = happyShift action_42
action_119 (83) = happyShift action_43
action_119 (84) = happyShift action_44
action_119 (87) = happyShift action_45
action_119 (88) = happyShift action_46
action_119 (89) = happyShift action_24
action_119 (26) = happyGoto action_29
action_119 (45) = happyGoto action_136
action_119 (46) = happyGoto action_31
action_119 (47) = happyGoto action_32
action_119 _ = happyFail (happyExpListPerState 119)

action_120 (57) = happyShift action_135
action_120 _ = happyFail (happyExpListPerState 120)

action_121 (50) = happyShift action_34
action_121 (58) = happyShift action_35
action_121 (59) = happyShift action_36
action_121 (67) = happyShift action_37
action_121 (73) = happyShift action_38
action_121 (75) = happyShift action_39
action_121 (80) = happyShift action_40
action_121 (81) = happyShift action_41
action_121 (82) = happyShift action_42
action_121 (83) = happyShift action_43
action_121 (84) = happyShift action_44
action_121 (87) = happyShift action_45
action_121 (88) = happyShift action_46
action_121 (89) = happyShift action_24
action_121 (26) = happyGoto action_29
action_121 (45) = happyGoto action_134
action_121 (46) = happyGoto action_31
action_121 (47) = happyGoto action_32
action_121 _ = happyFail (happyExpListPerState 121)

action_122 (50) = happyShift action_34
action_122 (58) = happyShift action_35
action_122 (59) = happyShift action_36
action_122 (67) = happyShift action_37
action_122 (73) = happyShift action_38
action_122 (75) = happyShift action_39
action_122 (80) = happyShift action_40
action_122 (81) = happyShift action_41
action_122 (82) = happyShift action_42
action_122 (83) = happyShift action_43
action_122 (84) = happyShift action_44
action_122 (87) = happyShift action_45
action_122 (88) = happyShift action_46
action_122 (89) = happyShift action_24
action_122 (26) = happyGoto action_29
action_122 (45) = happyGoto action_133
action_122 (46) = happyGoto action_31
action_122 (47) = happyGoto action_32
action_122 _ = happyFail (happyExpListPerState 122)

action_123 (51) = happyShift action_130
action_123 (52) = happyShift action_131
action_123 (54) = happyShift action_132
action_123 _ = happyFail (happyExpListPerState 123)

action_124 (50) = happyShift action_34
action_124 (58) = happyShift action_35
action_124 (59) = happyShift action_36
action_124 (67) = happyShift action_37
action_124 (73) = happyShift action_38
action_124 (75) = happyShift action_39
action_124 (80) = happyShift action_40
action_124 (81) = happyShift action_41
action_124 (82) = happyShift action_42
action_124 (83) = happyShift action_43
action_124 (84) = happyShift action_44
action_124 (87) = happyShift action_45
action_124 (88) = happyShift action_46
action_124 (89) = happyShift action_24
action_124 (26) = happyGoto action_29
action_124 (45) = happyGoto action_129
action_124 (46) = happyGoto action_31
action_124 (47) = happyGoto action_32
action_124 _ = happyFail (happyExpListPerState 124)

action_125 (50) = happyShift action_34
action_125 (58) = happyShift action_35
action_125 (59) = happyShift action_36
action_125 (67) = happyShift action_37
action_125 (73) = happyShift action_38
action_125 (75) = happyShift action_39
action_125 (80) = happyShift action_40
action_125 (81) = happyShift action_41
action_125 (82) = happyShift action_42
action_125 (83) = happyShift action_43
action_125 (84) = happyShift action_44
action_125 (87) = happyShift action_45
action_125 (88) = happyShift action_46
action_125 (89) = happyShift action_24
action_125 (26) = happyGoto action_29
action_125 (45) = happyGoto action_128
action_125 (46) = happyGoto action_31
action_125 (47) = happyGoto action_32
action_125 _ = happyFail (happyExpListPerState 125)

action_126 (52) = happyShift action_127
action_126 _ = happyFail (happyExpListPerState 126)

action_127 (50) = happyShift action_27
action_127 (60) = happyShift action_28
action_127 (89) = happyShift action_24
action_127 (26) = happyGoto action_25
action_127 (49) = happyGoto action_173
action_127 _ = happyFail (happyExpListPerState 127)

action_128 _ = happyReduce_65

action_129 _ = happyReduce_66

action_130 _ = happyReduce_81

action_131 (50) = happyShift action_34
action_131 (58) = happyShift action_35
action_131 (59) = happyShift action_36
action_131 (67) = happyShift action_37
action_131 (73) = happyShift action_38
action_131 (75) = happyShift action_39
action_131 (80) = happyShift action_40
action_131 (81) = happyShift action_41
action_131 (82) = happyShift action_42
action_131 (83) = happyShift action_43
action_131 (84) = happyShift action_44
action_131 (87) = happyShift action_45
action_131 (88) = happyShift action_46
action_131 (89) = happyShift action_24
action_131 (26) = happyGoto action_29
action_131 (45) = happyGoto action_172
action_131 (46) = happyGoto action_31
action_131 (47) = happyGoto action_32
action_131 _ = happyFail (happyExpListPerState 131)

action_132 (50) = happyShift action_34
action_132 (58) = happyShift action_35
action_132 (59) = happyShift action_36
action_132 (67) = happyShift action_37
action_132 (73) = happyShift action_38
action_132 (75) = happyShift action_39
action_132 (80) = happyShift action_40
action_132 (81) = happyShift action_41
action_132 (82) = happyShift action_42
action_132 (83) = happyShift action_43
action_132 (84) = happyShift action_44
action_132 (87) = happyShift action_45
action_132 (88) = happyShift action_46
action_132 (89) = happyShift action_24
action_132 (26) = happyGoto action_29
action_132 (45) = happyGoto action_171
action_132 (46) = happyGoto action_31
action_132 (47) = happyGoto action_32
action_132 _ = happyFail (happyExpListPerState 132)

action_133 (52) = happyShift action_170
action_133 _ = happyFail (happyExpListPerState 133)

action_134 (52) = happyShift action_169
action_134 _ = happyFail (happyExpListPerState 134)

action_135 (50) = happyShift action_34
action_135 (58) = happyShift action_35
action_135 (59) = happyShift action_36
action_135 (67) = happyShift action_37
action_135 (73) = happyShift action_38
action_135 (75) = happyShift action_39
action_135 (80) = happyShift action_40
action_135 (81) = happyShift action_41
action_135 (82) = happyShift action_42
action_135 (83) = happyShift action_43
action_135 (84) = happyShift action_44
action_135 (87) = happyShift action_45
action_135 (88) = happyShift action_46
action_135 (89) = happyShift action_24
action_135 (26) = happyGoto action_29
action_135 (45) = happyGoto action_168
action_135 (46) = happyGoto action_31
action_135 (47) = happyGoto action_32
action_135 _ = happyFail (happyExpListPerState 135)

action_136 (51) = happyShift action_167
action_136 _ = happyFail (happyExpListPerState 136)

action_137 (54) = happyShift action_166
action_137 _ = happyFail (happyExpListPerState 137)

action_138 (54) = happyShift action_165
action_138 _ = happyFail (happyExpListPerState 138)

action_139 (50) = happyShift action_34
action_139 (58) = happyShift action_35
action_139 (59) = happyShift action_36
action_139 (67) = happyShift action_37
action_139 (73) = happyShift action_38
action_139 (75) = happyShift action_39
action_139 (80) = happyShift action_40
action_139 (81) = happyShift action_41
action_139 (82) = happyShift action_42
action_139 (83) = happyShift action_43
action_139 (84) = happyShift action_44
action_139 (87) = happyShift action_45
action_139 (88) = happyShift action_46
action_139 (89) = happyShift action_24
action_139 (26) = happyGoto action_29
action_139 (45) = happyGoto action_30
action_139 (46) = happyGoto action_31
action_139 (47) = happyGoto action_32
action_139 (48) = happyGoto action_164
action_139 _ = happyFail (happyExpListPerState 139)

action_140 _ = happyReduce_60

action_141 (51) = happyShift action_163
action_141 _ = happyFail (happyExpListPerState 141)

action_142 _ = happyReduce_55

action_143 (50) = happyShift action_34
action_143 (58) = happyShift action_35
action_143 (59) = happyShift action_36
action_143 (67) = happyShift action_37
action_143 (73) = happyShift action_38
action_143 (75) = happyShift action_39
action_143 (80) = happyShift action_40
action_143 (81) = happyShift action_41
action_143 (82) = happyShift action_42
action_143 (83) = happyShift action_43
action_143 (84) = happyShift action_44
action_143 (87) = happyShift action_45
action_143 (88) = happyShift action_46
action_143 (89) = happyShift action_24
action_143 (26) = happyGoto action_29
action_143 (45) = happyGoto action_162
action_143 (46) = happyGoto action_31
action_143 (47) = happyGoto action_32
action_143 _ = happyFail (happyExpListPerState 143)

action_144 (54) = happyShift action_161
action_144 _ = happyFail (happyExpListPerState 144)

action_145 (77) = happyShift action_160
action_145 _ = happyFail (happyExpListPerState 145)

action_146 (71) = happyShift action_53
action_146 (43) = happyGoto action_159
action_146 _ = happyReduce_56

action_147 _ = happyReduce_46

action_148 (50) = happyShift action_34
action_148 (58) = happyShift action_35
action_148 (59) = happyShift action_36
action_148 (67) = happyShift action_37
action_148 (73) = happyShift action_38
action_148 (75) = happyShift action_39
action_148 (80) = happyShift action_40
action_148 (81) = happyShift action_41
action_148 (82) = happyShift action_42
action_148 (83) = happyShift action_43
action_148 (84) = happyShift action_44
action_148 (87) = happyShift action_45
action_148 (88) = happyShift action_46
action_148 (89) = happyShift action_24
action_148 (26) = happyGoto action_29
action_148 (45) = happyGoto action_158
action_148 (46) = happyGoto action_31
action_148 (47) = happyGoto action_32
action_148 _ = happyFail (happyExpListPerState 148)

action_149 (50) = happyShift action_69
action_149 (37) = happyGoto action_67
action_149 (38) = happyGoto action_157
action_149 _ = happyReduce_42

action_150 _ = happyReduce_35

action_151 _ = happyReduce_38

action_152 (78) = happyShift action_156
action_152 _ = happyFail (happyExpListPerState 152)

action_153 _ = happyReduce_30

action_154 (50) = happyShift action_69
action_154 (37) = happyGoto action_67
action_154 (38) = happyGoto action_155
action_154 _ = happyReduce_42

action_155 (56) = happyShift action_188
action_155 _ = happyFail (happyExpListPerState 155)

action_156 _ = happyReduce_34

action_157 (56) = happyShift action_187
action_157 _ = happyFail (happyExpListPerState 157)

action_158 (51) = happyShift action_185
action_158 (55) = happyShift action_186
action_158 _ = happyFail (happyExpListPerState 158)

action_159 (54) = happyShift action_184
action_159 _ = happyFail (happyExpListPerState 159)

action_160 (61) = happyShift action_56
action_160 (62) = happyShift action_57
action_160 (63) = happyShift action_58
action_160 (69) = happyShift action_59
action_160 (70) = happyShift action_60
action_160 (72) = happyShift action_61
action_160 (41) = happyGoto action_54
action_160 (42) = happyGoto action_183
action_160 _ = happyReduce_53

action_161 (50) = happyShift action_34
action_161 (58) = happyShift action_35
action_161 (59) = happyShift action_36
action_161 (67) = happyShift action_37
action_161 (73) = happyShift action_38
action_161 (75) = happyShift action_39
action_161 (80) = happyShift action_40
action_161 (81) = happyShift action_41
action_161 (82) = happyShift action_42
action_161 (83) = happyShift action_43
action_161 (84) = happyShift action_44
action_161 (87) = happyShift action_45
action_161 (88) = happyShift action_46
action_161 (89) = happyShift action_24
action_161 (26) = happyGoto action_29
action_161 (45) = happyGoto action_182
action_161 (46) = happyGoto action_31
action_161 (47) = happyGoto action_32
action_161 _ = happyFail (happyExpListPerState 161)

action_162 _ = happyReduce_51

action_163 _ = happyReduce_57

action_164 _ = happyReduce_63

action_165 (50) = happyShift action_34
action_165 (58) = happyShift action_35
action_165 (59) = happyShift action_36
action_165 (67) = happyShift action_37
action_165 (73) = happyShift action_38
action_165 (75) = happyShift action_39
action_165 (80) = happyShift action_40
action_165 (81) = happyShift action_41
action_165 (82) = happyShift action_42
action_165 (83) = happyShift action_43
action_165 (84) = happyShift action_44
action_165 (87) = happyShift action_45
action_165 (88) = happyShift action_46
action_165 (89) = happyShift action_24
action_165 (26) = happyGoto action_29
action_165 (45) = happyGoto action_181
action_165 (46) = happyGoto action_31
action_165 (47) = happyGoto action_32
action_165 _ = happyFail (happyExpListPerState 165)

action_166 (50) = happyShift action_34
action_166 (58) = happyShift action_35
action_166 (59) = happyShift action_36
action_166 (67) = happyShift action_37
action_166 (73) = happyShift action_38
action_166 (75) = happyShift action_39
action_166 (80) = happyShift action_40
action_166 (81) = happyShift action_41
action_166 (82) = happyShift action_42
action_166 (83) = happyShift action_43
action_166 (84) = happyShift action_44
action_166 (87) = happyShift action_45
action_166 (88) = happyShift action_46
action_166 (89) = happyShift action_24
action_166 (26) = happyGoto action_29
action_166 (45) = happyGoto action_180
action_166 (46) = happyGoto action_31
action_166 (47) = happyGoto action_32
action_166 _ = happyFail (happyExpListPerState 166)

action_167 _ = happyReduce_77

action_168 (65) = happyShift action_179
action_168 _ = happyFail (happyExpListPerState 168)

action_169 (50) = happyShift action_34
action_169 (58) = happyShift action_35
action_169 (59) = happyShift action_36
action_169 (67) = happyShift action_37
action_169 (73) = happyShift action_38
action_169 (75) = happyShift action_39
action_169 (80) = happyShift action_40
action_169 (81) = happyShift action_41
action_169 (82) = happyShift action_42
action_169 (83) = happyShift action_43
action_169 (84) = happyShift action_44
action_169 (87) = happyShift action_45
action_169 (88) = happyShift action_46
action_169 (89) = happyShift action_24
action_169 (26) = happyGoto action_29
action_169 (45) = happyGoto action_178
action_169 (46) = happyGoto action_31
action_169 (47) = happyGoto action_32
action_169 _ = happyFail (happyExpListPerState 169)

action_170 (50) = happyShift action_34
action_170 (58) = happyShift action_35
action_170 (59) = happyShift action_36
action_170 (67) = happyShift action_37
action_170 (73) = happyShift action_38
action_170 (75) = happyShift action_39
action_170 (80) = happyShift action_40
action_170 (81) = happyShift action_41
action_170 (82) = happyShift action_42
action_170 (83) = happyShift action_43
action_170 (84) = happyShift action_44
action_170 (87) = happyShift action_45
action_170 (88) = happyShift action_46
action_170 (89) = happyShift action_24
action_170 (26) = happyGoto action_29
action_170 (45) = happyGoto action_177
action_170 (46) = happyGoto action_31
action_170 (47) = happyGoto action_32
action_170 _ = happyFail (happyExpListPerState 170)

action_171 (51) = happyShift action_176
action_171 _ = happyFail (happyExpListPerState 171)

action_172 (51) = happyShift action_175
action_172 _ = happyFail (happyExpListPerState 172)

action_173 (51) = happyShift action_174
action_173 _ = happyFail (happyExpListPerState 173)

action_174 _ = happyReduce_85

action_175 _ = happyReduce_79

action_176 _ = happyReduce_80

action_177 (52) = happyShift action_198
action_177 _ = happyFail (happyExpListPerState 177)

action_178 (52) = happyShift action_197
action_178 _ = happyFail (happyExpListPerState 178)

action_179 (50) = happyShift action_34
action_179 (58) = happyShift action_35
action_179 (59) = happyShift action_36
action_179 (67) = happyShift action_37
action_179 (73) = happyShift action_38
action_179 (75) = happyShift action_39
action_179 (80) = happyShift action_40
action_179 (81) = happyShift action_41
action_179 (82) = happyShift action_42
action_179 (83) = happyShift action_43
action_179 (84) = happyShift action_44
action_179 (87) = happyShift action_45
action_179 (88) = happyShift action_46
action_179 (89) = happyShift action_24
action_179 (26) = happyGoto action_29
action_179 (45) = happyGoto action_30
action_179 (46) = happyGoto action_31
action_179 (47) = happyGoto action_32
action_179 (48) = happyGoto action_196
action_179 _ = happyFail (happyExpListPerState 179)

action_180 (51) = happyShift action_195
action_180 _ = happyFail (happyExpListPerState 180)

action_181 (51) = happyShift action_194
action_181 _ = happyFail (happyExpListPerState 181)

action_182 (55) = happyShift action_193
action_182 _ = happyFail (happyExpListPerState 182)

action_183 (78) = happyShift action_192
action_183 _ = happyFail (happyExpListPerState 183)

action_184 (50) = happyShift action_34
action_184 (58) = happyShift action_35
action_184 (59) = happyShift action_36
action_184 (67) = happyShift action_37
action_184 (73) = happyShift action_38
action_184 (75) = happyShift action_39
action_184 (80) = happyShift action_40
action_184 (81) = happyShift action_41
action_184 (82) = happyShift action_42
action_184 (83) = happyShift action_43
action_184 (84) = happyShift action_44
action_184 (87) = happyShift action_45
action_184 (88) = happyShift action_46
action_184 (89) = happyShift action_24
action_184 (26) = happyGoto action_29
action_184 (45) = happyGoto action_191
action_184 (46) = happyGoto action_31
action_184 (47) = happyGoto action_32
action_184 _ = happyFail (happyExpListPerState 184)

action_185 _ = happyReduce_40

action_186 (50) = happyShift action_34
action_186 (58) = happyShift action_35
action_186 (59) = happyShift action_36
action_186 (67) = happyShift action_37
action_186 (73) = happyShift action_38
action_186 (75) = happyShift action_39
action_186 (80) = happyShift action_40
action_186 (81) = happyShift action_41
action_186 (82) = happyShift action_42
action_186 (83) = happyShift action_43
action_186 (84) = happyShift action_44
action_186 (87) = happyShift action_45
action_186 (88) = happyShift action_46
action_186 (89) = happyShift action_24
action_186 (26) = happyGoto action_29
action_186 (45) = happyGoto action_190
action_186 (46) = happyGoto action_31
action_186 (47) = happyGoto action_32
action_186 _ = happyFail (happyExpListPerState 186)

action_187 _ = happyReduce_39

action_188 (64) = happyShift action_65
action_188 (39) = happyGoto action_63
action_188 (40) = happyGoto action_189
action_188 _ = happyReduce_45

action_189 (61) = happyShift action_56
action_189 (62) = happyShift action_57
action_189 (63) = happyShift action_58
action_189 (69) = happyShift action_59
action_189 (70) = happyShift action_60
action_189 (72) = happyShift action_61
action_189 (41) = happyGoto action_54
action_189 (42) = happyGoto action_206
action_189 _ = happyReduce_53

action_190 (51) = happyShift action_205
action_190 _ = happyFail (happyExpListPerState 190)

action_191 (55) = happyShift action_204
action_191 _ = happyFail (happyExpListPerState 191)

action_192 _ = happyReduce_49

action_193 (50) = happyShift action_34
action_193 (58) = happyShift action_35
action_193 (59) = happyShift action_36
action_193 (67) = happyShift action_37
action_193 (73) = happyShift action_38
action_193 (75) = happyShift action_39
action_193 (80) = happyShift action_40
action_193 (81) = happyShift action_41
action_193 (82) = happyShift action_42
action_193 (83) = happyShift action_43
action_193 (84) = happyShift action_44
action_193 (87) = happyShift action_45
action_193 (88) = happyShift action_46
action_193 (89) = happyShift action_24
action_193 (26) = happyGoto action_29
action_193 (45) = happyGoto action_203
action_193 (46) = happyGoto action_31
action_193 (47) = happyGoto action_32
action_193 _ = happyFail (happyExpListPerState 193)

action_194 (79) = happyShift action_202
action_194 _ = happyFail (happyExpListPerState 194)

action_195 (85) = happyShift action_201
action_195 _ = happyFail (happyExpListPerState 195)

action_196 _ = happyReduce_64

action_197 (50) = happyShift action_34
action_197 (58) = happyShift action_35
action_197 (59) = happyShift action_36
action_197 (67) = happyShift action_37
action_197 (73) = happyShift action_38
action_197 (75) = happyShift action_39
action_197 (80) = happyShift action_40
action_197 (81) = happyShift action_41
action_197 (82) = happyShift action_42
action_197 (83) = happyShift action_43
action_197 (84) = happyShift action_44
action_197 (87) = happyShift action_45
action_197 (88) = happyShift action_46
action_197 (89) = happyShift action_24
action_197 (26) = happyGoto action_29
action_197 (45) = happyGoto action_200
action_197 (46) = happyGoto action_31
action_197 (47) = happyGoto action_32
action_197 _ = happyFail (happyExpListPerState 197)

action_198 (50) = happyShift action_34
action_198 (58) = happyShift action_35
action_198 (59) = happyShift action_36
action_198 (67) = happyShift action_37
action_198 (73) = happyShift action_38
action_198 (75) = happyShift action_39
action_198 (80) = happyShift action_40
action_198 (81) = happyShift action_41
action_198 (82) = happyShift action_42
action_198 (83) = happyShift action_43
action_198 (84) = happyShift action_44
action_198 (87) = happyShift action_45
action_198 (88) = happyShift action_46
action_198 (89) = happyShift action_24
action_198 (26) = happyGoto action_29
action_198 (45) = happyGoto action_199
action_198 (46) = happyGoto action_31
action_198 (47) = happyGoto action_32
action_198 _ = happyFail (happyExpListPerState 198)

action_199 (51) = happyShift action_211
action_199 _ = happyFail (happyExpListPerState 199)

action_200 (51) = happyShift action_210
action_200 _ = happyFail (happyExpListPerState 200)

action_201 (50) = happyShift action_34
action_201 (58) = happyShift action_35
action_201 (59) = happyShift action_36
action_201 (67) = happyShift action_37
action_201 (73) = happyShift action_38
action_201 (75) = happyShift action_39
action_201 (80) = happyShift action_40
action_201 (81) = happyShift action_41
action_201 (82) = happyShift action_42
action_201 (83) = happyShift action_43
action_201 (84) = happyShift action_44
action_201 (87) = happyShift action_45
action_201 (88) = happyShift action_46
action_201 (89) = happyShift action_24
action_201 (26) = happyGoto action_29
action_201 (45) = happyGoto action_30
action_201 (46) = happyGoto action_31
action_201 (47) = happyGoto action_32
action_201 (48) = happyGoto action_209
action_201 _ = happyFail (happyExpListPerState 201)

action_202 (50) = happyShift action_34
action_202 (58) = happyShift action_35
action_202 (59) = happyShift action_36
action_202 (67) = happyShift action_37
action_202 (73) = happyShift action_38
action_202 (75) = happyShift action_39
action_202 (80) = happyShift action_40
action_202 (81) = happyShift action_41
action_202 (82) = happyShift action_42
action_202 (83) = happyShift action_43
action_202 (84) = happyShift action_44
action_202 (87) = happyShift action_45
action_202 (88) = happyShift action_46
action_202 (89) = happyShift action_24
action_202 (26) = happyGoto action_29
action_202 (45) = happyGoto action_30
action_202 (46) = happyGoto action_31
action_202 (47) = happyGoto action_32
action_202 (48) = happyGoto action_208
action_202 _ = happyFail (happyExpListPerState 202)

action_203 _ = happyReduce_47

action_204 (50) = happyShift action_34
action_204 (58) = happyShift action_35
action_204 (59) = happyShift action_36
action_204 (67) = happyShift action_37
action_204 (73) = happyShift action_38
action_204 (75) = happyShift action_39
action_204 (80) = happyShift action_40
action_204 (81) = happyShift action_41
action_204 (82) = happyShift action_42
action_204 (83) = happyShift action_43
action_204 (84) = happyShift action_44
action_204 (87) = happyShift action_45
action_204 (88) = happyShift action_46
action_204 (89) = happyShift action_24
action_204 (26) = happyGoto action_29
action_204 (45) = happyGoto action_207
action_204 (46) = happyGoto action_31
action_204 (47) = happyGoto action_32
action_204 _ = happyFail (happyExpListPerState 204)

action_205 _ = happyReduce_41

action_206 _ = happyReduce_29

action_207 _ = happyReduce_48

action_208 _ = happyReduce_62

action_209 _ = happyReduce_61

action_210 _ = happyReduce_78

action_211 _ = happyReduce_76

happyReduce_23 = happySpecReduce_1  26 happyReduction_23
happyReduction_23 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn26
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.VarIdent (tokenText happy_var_1))
	)
happyReduction_23 _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_1  27 happyReduction_24
happyReduction_24 (HappyAbsSyn28  happy_var_1)
	 =  HappyAbsSyn27
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AProgram (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_24 _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_0  28 happyReduction_25
happyReduction_25  =  HappyAbsSyn28
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_26 = happySpecReduce_2  28 happyReduction_26
happyReduction_26 (HappyAbsSyn28  happy_var_2)
	(HappyAbsSyn29  happy_var_1)
	 =  HappyAbsSyn28
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_26 _ _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_1  29 happyReduction_27
happyReduction_27 (HappyAbsSyn30  happy_var_1)
	 =  HappyAbsSyn29
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.UnitModule (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_27 _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_1  29 happyReduction_28
happyReduction_28 (HappyAbsSyn36  happy_var_1)
	 =  HappyAbsSyn29
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.UnitTelescope (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_28 _  = notHappyAtAll 

happyReduce_29 = happyReduce 7 30 happyReduction_29
happyReduction_29 ((HappyAbsSyn42  happy_var_7) `HappyStk`
	(HappyAbsSyn40  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn38  happy_var_4) `HappyStk`
	(HappyAbsSyn32  happy_var_3) `HappyStk`
	(HappyAbsSyn26  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn30
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AModule (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_4) (snd happy_var_6) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_30 = happySpecReduce_3  31 happyReduction_30
happyReduction_30 (HappyAbsSyn33  happy_var_3)
	(HappyAbsSyn26  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AnInclude (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3))
	)
happyReduction_30 _ _ _  = notHappyAtAll 

happyReduce_31 = happySpecReduce_0  32 happyReduction_31
happyReduction_31  =  HappyAbsSyn32
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_32 = happySpecReduce_2  32 happyReduction_32
happyReduction_32 (HappyAbsSyn32  happy_var_2)
	(HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn32
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_32 _ _  = notHappyAtAll 

happyReduce_33 = happySpecReduce_0  33 happyReduction_33
happyReduction_33  =  HappyAbsSyn33
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, Language.MLTT.Syntax.Abs.NoRefinement Language.MLTT.Syntax.Abs.BNFC'NoPosition)
	)

happyReduce_34 = happyReduce 4 33 happyReduction_34
happyReduction_34 (_ `HappyStk`
	(HappyAbsSyn35  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn33
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.ARefinement (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_35 = happySpecReduce_3  34 happyReduction_35
happyReduction_35 (HappyAbsSyn45  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn34
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AFixed (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_35 _ _ _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_0  35 happyReduction_36
happyReduction_36  =  HappyAbsSyn35
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_37 = happySpecReduce_1  35 happyReduction_37
happyReduction_37 (HappyAbsSyn34  happy_var_1)
	 =  HappyAbsSyn35
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_37 _  = notHappyAtAll 

happyReduce_38 = happySpecReduce_3  35 happyReduction_38
happyReduction_38 (HappyAbsSyn35  happy_var_3)
	_
	(HappyAbsSyn34  happy_var_1)
	 =  HappyAbsSyn35
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_38 _ _ _  = notHappyAtAll 

happyReduce_39 = happyReduce 5 36 happyReduction_39
happyReduction_39 (_ `HappyStk`
	(HappyAbsSyn38  happy_var_4) `HappyStk`
	(HappyAbsSyn32  happy_var_3) `HappyStk`
	(HappyAbsSyn26  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn36
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.ATelescope (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_40 = happyReduce 5 37 happyReduction_40
happyReduction_40 (_ `HappyStk`
	(HappyAbsSyn45  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn26  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn37
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AParam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_41 = happyReduce 7 37 happyReduction_41
happyReduction_41 (_ `HappyStk`
	(HappyAbsSyn45  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn26  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn37
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AManifest (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_42 = happySpecReduce_0  38 happyReduction_42
happyReduction_42  =  HappyAbsSyn38
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_43 = happySpecReduce_2  38 happyReduction_43
happyReduction_43 (HappyAbsSyn38  happy_var_2)
	(HappyAbsSyn37  happy_var_1)
	 =  HappyAbsSyn38
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_43 _ _  = notHappyAtAll 

happyReduce_44 = happySpecReduce_2  39 happyReduction_44
happyReduction_44 (HappyAbsSyn26  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn39
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AnImport (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_44 _ _  = notHappyAtAll 

happyReduce_45 = happySpecReduce_0  40 happyReduction_45
happyReduction_45  =  HappyAbsSyn40
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_46 = happySpecReduce_3  40 happyReduction_46
happyReduction_46 (HappyAbsSyn40  happy_var_3)
	_
	(HappyAbsSyn39  happy_var_1)
	 =  HappyAbsSyn40
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_46 _ _ _  = notHappyAtAll 

happyReduce_47 = happyReduce 7 41 happyReduction_47
happyReduction_47 ((HappyAbsSyn45  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn43  happy_var_3) `HappyStk`
	(HappyAbsSyn26  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn41
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_48 = happyReduce 8 41 happyReduction_48
happyReduction_48 ((HappyAbsSyn45  happy_var_8) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn43  happy_var_4) `HappyStk`
	(HappyAbsSyn26  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn41
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclPrivateDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_4) (snd happy_var_6) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_49 = happyReduce 6 41 happyReduction_49
happyReduction_49 (_ `HappyStk`
	(HappyAbsSyn42  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn26  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn41
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclNamespace (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_5))
	) `HappyStk` happyRest

happyReduce_50 = happySpecReduce_2  41 happyReduction_50
happyReduction_50 (HappyAbsSyn26  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn41
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclOpen (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_50 _ _  = notHappyAtAll 

happyReduce_51 = happyReduce 4 41 happyReduction_51
happyReduction_51 ((HappyAbsSyn45  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn41
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCheck (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_52 = happySpecReduce_2  41 happyReduction_52
happyReduction_52 (HappyAbsSyn45  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn41
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCompute (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_52 _ _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_0  42 happyReduction_53
happyReduction_53  =  HappyAbsSyn42
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_54 = happySpecReduce_1  42 happyReduction_54
happyReduction_54 (HappyAbsSyn41  happy_var_1)
	 =  HappyAbsSyn42
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_54 _  = notHappyAtAll 

happyReduce_55 = happySpecReduce_3  42 happyReduction_55
happyReduction_55 (HappyAbsSyn42  happy_var_3)
	_
	(HappyAbsSyn41  happy_var_1)
	 =  HappyAbsSyn42
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_55 _ _ _  = notHappyAtAll 

happyReduce_56 = happySpecReduce_0  43 happyReduction_56
happyReduction_56  =  HappyAbsSyn43
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, Language.MLTT.Syntax.Abs.NoDischarge Language.MLTT.Syntax.Abs.BNFC'NoPosition)
	)

happyReduce_57 = happyReduce 4 43 happyReduction_57
happyReduction_57 (_ `HappyStk`
	(HappyAbsSyn44  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn43
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DischargeOver (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_58 = happySpecReduce_0  44 happyReduction_58
happyReduction_58  =  HappyAbsSyn44
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_59 = happySpecReduce_1  44 happyReduction_59
happyReduction_59 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn44
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_59 _  = notHappyAtAll 

happyReduce_60 = happySpecReduce_3  44 happyReduction_60
happyReduction_60 (HappyAbsSyn44  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn44
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_60 _ _ _  = notHappyAtAll 

happyReduce_61 = happyReduce 8 45 happyReduction_61
happyReduction_61 ((HappyAbsSyn48  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn49  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pi (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_62 = happyReduce 8 45 happyReduction_62
happyReduction_62 ((HappyAbsSyn48  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn49  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Sigma (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_63 = happyReduce 4 45 happyReduction_63
happyReduction_63 ((HappyAbsSyn48  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn49  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Lam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_64 = happyReduce 6 45 happyReduction_64
happyReduction_64 ((HappyAbsSyn48  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn49  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Let (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_65 = happySpecReduce_3  45 happyReduction_65
happyReduction_65 (HappyAbsSyn45  happy_var_3)
	_
	(HappyAbsSyn45  happy_var_1)
	 =  HappyAbsSyn45
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Arrow (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_65 _ _ _  = notHappyAtAll 

happyReduce_66 = happySpecReduce_3  45 happyReduction_66
happyReduction_66 (HappyAbsSyn45  happy_var_3)
	_
	(HappyAbsSyn45  happy_var_1)
	 =  HappyAbsSyn45
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Product (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_66 _ _ _  = notHappyAtAll 

happyReduce_67 = happySpecReduce_1  45 happyReduction_67
happyReduction_67 (HappyAbsSyn45  happy_var_1)
	 =  HappyAbsSyn45
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_67 _  = notHappyAtAll 

happyReduce_68 = happySpecReduce_2  46 happyReduction_68
happyReduction_68 (HappyAbsSyn45  happy_var_2)
	(HappyAbsSyn45  happy_var_1)
	 =  HappyAbsSyn45
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.App (fst happy_var_1) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_68 _ _  = notHappyAtAll 

happyReduce_69 = happySpecReduce_1  46 happyReduction_69
happyReduction_69 (HappyAbsSyn45  happy_var_1)
	 =  HappyAbsSyn45
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_69 _  = notHappyAtAll 

happyReduce_70 = happySpecReduce_2  47 happyReduction_70
happyReduction_70 (HappyAbsSyn45  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.First (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_70 _ _  = notHappyAtAll 

happyReduce_71 = happySpecReduce_2  47 happyReduction_71
happyReduction_71 (HappyAbsSyn45  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Second (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_71 _ _  = notHappyAtAll 

happyReduce_72 = happySpecReduce_1  47 happyReduction_72
happyReduction_72 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Universe (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_72 _  = notHappyAtAll 

happyReduce_73 = happySpecReduce_1  47 happyReduction_73
happyReduction_73 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_73 _  = notHappyAtAll 

happyReduce_74 = happySpecReduce_1  47 happyReduction_74
happyReduction_74 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitVal (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_74 _  = notHappyAtAll 

happyReduce_75 = happySpecReduce_1  47 happyReduction_75
happyReduction_75 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn45
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Var (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_75 _  = notHappyAtAll 

happyReduce_76 = happyReduce 8 47 happyReduction_76
happyReduction_76 (_ `HappyStk`
	(HappyAbsSyn45  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.IdType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_77 = happyReduce 4 47 happyReduction_77
happyReduction_77 (_ `HappyStk`
	(HappyAbsSyn45  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Refl (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_78 = happyReduce 8 47 happyReduction_78
happyReduction_78 (_ `HappyStk`
	(HappyAbsSyn45  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.J (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_79 = happyReduce 5 47 happyReduction_79
happyReduction_79 (_ `HappyStk`
	(HappyAbsSyn45  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_80 = happyReduce 5 47 happyReduction_80
happyReduction_80 (_ `HappyStk`
	(HappyAbsSyn45  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn45  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Ann (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_81 = happySpecReduce_3  47 happyReduction_81
happyReduction_81 _
	(HappyAbsSyn45  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn45
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), (snd happy_var_2))
	)
happyReduction_81 _ _ _  = notHappyAtAll 

happyReduce_82 = happySpecReduce_1  48 happyReduction_82
happyReduction_82 (HappyAbsSyn45  happy_var_1)
	 =  HappyAbsSyn48
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AScopedTerm (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_82 _  = notHappyAtAll 

happyReduce_83 = happySpecReduce_1  49 happyReduction_83
happyReduction_83 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn49
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternWildcard (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_83 _  = notHappyAtAll 

happyReduce_84 = happySpecReduce_1  49 happyReduction_84
happyReduction_84 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn49
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.PatternVar (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_84 _  = notHappyAtAll 

happyReduce_85 = happyReduce 5 49 happyReduction_85
happyReduction_85 (_ `HappyStk`
	(HappyAbsSyn49  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn49  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn49
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternPair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyNewToken action sts stk [] =
	action 90 90 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 50;
	PT _ (TS _ 2) -> cont 51;
	PT _ (TS _ 3) -> cont 52;
	PT _ (TS _ 4) -> cont 53;
	PT _ (TS _ 5) -> cont 54;
	PT _ (TS _ 6) -> cont 55;
	PT _ (TS _ 7) -> cont 56;
	PT _ (TS _ 8) -> cont 57;
	PT _ (TS _ 9) -> cont 58;
	PT _ (TS _ 10) -> cont 59;
	PT _ (TS _ 11) -> cont 60;
	PT _ (TS _ 12) -> cont 61;
	PT _ (TS _ 13) -> cont 62;
	PT _ (TS _ 14) -> cont 63;
	PT _ (TS _ 15) -> cont 64;
	PT _ (TS _ 16) -> cont 65;
	PT _ (TS _ 17) -> cont 66;
	PT _ (TS _ 18) -> cont 67;
	PT _ (TS _ 19) -> cont 68;
	PT _ (TS _ 20) -> cont 69;
	PT _ (TS _ 21) -> cont 70;
	PT _ (TS _ 22) -> cont 71;
	PT _ (TS _ 23) -> cont 72;
	PT _ (TS _ 24) -> cont 73;
	PT _ (TS _ 25) -> cont 74;
	PT _ (TS _ 26) -> cont 75;
	PT _ (TS _ 27) -> cont 76;
	PT _ (TS _ 28) -> cont 77;
	PT _ (TS _ 29) -> cont 78;
	PT _ (TS _ 30) -> cont 79;
	PT _ (TS _ 31) -> cont 80;
	PT _ (TS _ 32) -> cont 81;
	PT _ (TS _ 33) -> cont 82;
	PT _ (TS _ 34) -> cont 83;
	PT _ (TS _ 35) -> cont 84;
	PT _ (TS _ 36) -> cont 85;
	PT _ (TS _ 37) -> cont 86;
	PT _ (TS _ 38) -> cont 87;
	PT _ (TS _ 39) -> cont 88;
	PT _ (T_VarIdent _) -> cont 89;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 90 tk tks = happyError' (tks, explist)
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
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn27 z -> happyReturn z; _other -> notHappyAtAll })

pListUnit_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn28 z -> happyReturn z; _other -> notHappyAtAll })

pUnit_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_2 tks) (\x -> case x of {HappyAbsSyn29 z -> happyReturn z; _other -> notHappyAtAll })

pModule_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_3 tks) (\x -> case x of {HappyAbsSyn30 z -> happyReturn z; _other -> notHappyAtAll })

pInclude_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_4 tks) (\x -> case x of {HappyAbsSyn31 z -> happyReturn z; _other -> notHappyAtAll })

pListInclude_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_5 tks) (\x -> case x of {HappyAbsSyn32 z -> happyReturn z; _other -> notHappyAtAll })

pRefinement_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_6 tks) (\x -> case x of {HappyAbsSyn33 z -> happyReturn z; _other -> notHappyAtAll })

pFixed_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_7 tks) (\x -> case x of {HappyAbsSyn34 z -> happyReturn z; _other -> notHappyAtAll })

pListFixed_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_8 tks) (\x -> case x of {HappyAbsSyn35 z -> happyReturn z; _other -> notHappyAtAll })

pTelescopeDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_9 tks) (\x -> case x of {HappyAbsSyn36 z -> happyReturn z; _other -> notHappyAtAll })

pParam_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_10 tks) (\x -> case x of {HappyAbsSyn37 z -> happyReturn z; _other -> notHappyAtAll })

pListParam_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_11 tks) (\x -> case x of {HappyAbsSyn38 z -> happyReturn z; _other -> notHappyAtAll })

pImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_12 tks) (\x -> case x of {HappyAbsSyn39 z -> happyReturn z; _other -> notHappyAtAll })

pListImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_13 tks) (\x -> case x of {HappyAbsSyn40 z -> happyReturn z; _other -> notHappyAtAll })

pDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_14 tks) (\x -> case x of {HappyAbsSyn41 z -> happyReturn z; _other -> notHappyAtAll })

pListDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_15 tks) (\x -> case x of {HappyAbsSyn42 z -> happyReturn z; _other -> notHappyAtAll })

pDischarge_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_16 tks) (\x -> case x of {HappyAbsSyn43 z -> happyReturn z; _other -> notHappyAtAll })

pListVarIdent_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_17 tks) (\x -> case x of {HappyAbsSyn44 z -> happyReturn z; _other -> notHappyAtAll })

pTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_18 tks) (\x -> case x of {HappyAbsSyn45 z -> happyReturn z; _other -> notHappyAtAll })

pTerm1_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_19 tks) (\x -> case x of {HappyAbsSyn45 z -> happyReturn z; _other -> notHappyAtAll })

pTerm2_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_20 tks) (\x -> case x of {HappyAbsSyn45 z -> happyReturn z; _other -> notHappyAtAll })

pScopedTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_21 tks) (\x -> case x of {HappyAbsSyn48 z -> happyReturn z; _other -> notHappyAtAll })

pPattern_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_22 tks) (\x -> case x of {HappyAbsSyn49 z -> happyReturn z; _other -> notHappyAtAll })

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

pListUnit :: [Token] -> Err [Language.MLTT.Syntax.Abs.Unit]
pListUnit = fmap snd . pListUnit_internal

pUnit :: [Token] -> Err Language.MLTT.Syntax.Abs.Unit
pUnit = fmap snd . pUnit_internal

pModule :: [Token] -> Err Language.MLTT.Syntax.Abs.Module
pModule = fmap snd . pModule_internal

pInclude :: [Token] -> Err Language.MLTT.Syntax.Abs.Include
pInclude = fmap snd . pInclude_internal

pListInclude :: [Token] -> Err [Language.MLTT.Syntax.Abs.Include]
pListInclude = fmap snd . pListInclude_internal

pRefinement :: [Token] -> Err Language.MLTT.Syntax.Abs.Refinement
pRefinement = fmap snd . pRefinement_internal

pFixed :: [Token] -> Err Language.MLTT.Syntax.Abs.Fixed
pFixed = fmap snd . pFixed_internal

pListFixed :: [Token] -> Err [Language.MLTT.Syntax.Abs.Fixed]
pListFixed = fmap snd . pListFixed_internal

pTelescopeDecl :: [Token] -> Err Language.MLTT.Syntax.Abs.TelescopeDecl
pTelescopeDecl = fmap snd . pTelescopeDecl_internal

pParam :: [Token] -> Err Language.MLTT.Syntax.Abs.Param
pParam = fmap snd . pParam_internal

pListParam :: [Token] -> Err [Language.MLTT.Syntax.Abs.Param]
pListParam = fmap snd . pListParam_internal

pImport :: [Token] -> Err Language.MLTT.Syntax.Abs.Import
pImport = fmap snd . pImport_internal

pListImport :: [Token] -> Err [Language.MLTT.Syntax.Abs.Import]
pListImport = fmap snd . pListImport_internal

pDecl :: [Token] -> Err Language.MLTT.Syntax.Abs.Decl
pDecl = fmap snd . pDecl_internal

pListDecl :: [Token] -> Err [Language.MLTT.Syntax.Abs.Decl]
pListDecl = fmap snd . pListDecl_internal

pDischarge :: [Token] -> Err Language.MLTT.Syntax.Abs.Discharge
pDischarge = fmap snd . pDischarge_internal

pListVarIdent :: [Token] -> Err [Language.MLTT.Syntax.Abs.VarIdent]
pListVarIdent = fmap snd . pListVarIdent_internal

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
