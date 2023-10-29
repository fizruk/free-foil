// Generated from org/syntax/lambdapi/simple/SimpleParser.g4 by ANTLR 4.9.3
package org.syntax.lambdapi.simple;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link SimpleParser}.
 */
public interface SimpleParserListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link SimpleParser#start_Program}.
	 * @param ctx the parse tree
	 */
	void enterStart_Program(SimpleParser.Start_ProgramContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#start_Program}.
	 * @param ctx the parse tree
	 */
	void exitStart_Program(SimpleParser.Start_ProgramContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleParser#start_Command}.
	 * @param ctx the parse tree
	 */
	void enterStart_Command(SimpleParser.Start_CommandContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#start_Command}.
	 * @param ctx the parse tree
	 */
	void exitStart_Command(SimpleParser.Start_CommandContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleParser#start_ListCommand}.
	 * @param ctx the parse tree
	 */
	void enterStart_ListCommand(SimpleParser.Start_ListCommandContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#start_ListCommand}.
	 * @param ctx the parse tree
	 */
	void exitStart_ListCommand(SimpleParser.Start_ListCommandContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleParser#start_Term}.
	 * @param ctx the parse tree
	 */
	void enterStart_Term(SimpleParser.Start_TermContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#start_Term}.
	 * @param ctx the parse tree
	 */
	void exitStart_Term(SimpleParser.Start_TermContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleParser#start_Term1}.
	 * @param ctx the parse tree
	 */
	void enterStart_Term1(SimpleParser.Start_Term1Context ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#start_Term1}.
	 * @param ctx the parse tree
	 */
	void exitStart_Term1(SimpleParser.Start_Term1Context ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleParser#start_Term2}.
	 * @param ctx the parse tree
	 */
	void enterStart_Term2(SimpleParser.Start_Term2Context ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#start_Term2}.
	 * @param ctx the parse tree
	 */
	void exitStart_Term2(SimpleParser.Start_Term2Context ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleParser#program}.
	 * @param ctx the parse tree
	 */
	void enterProgram(SimpleParser.ProgramContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#program}.
	 * @param ctx the parse tree
	 */
	void exitProgram(SimpleParser.ProgramContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleParser#command}.
	 * @param ctx the parse tree
	 */
	void enterCommand(SimpleParser.CommandContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#command}.
	 * @param ctx the parse tree
	 */
	void exitCommand(SimpleParser.CommandContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleParser#listCommand}.
	 * @param ctx the parse tree
	 */
	void enterListCommand(SimpleParser.ListCommandContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#listCommand}.
	 * @param ctx the parse tree
	 */
	void exitListCommand(SimpleParser.ListCommandContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleParser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm(SimpleParser.TermContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm(SimpleParser.TermContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleParser#term1}.
	 * @param ctx the parse tree
	 */
	void enterTerm1(SimpleParser.Term1Context ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#term1}.
	 * @param ctx the parse tree
	 */
	void exitTerm1(SimpleParser.Term1Context ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleParser#term2}.
	 * @param ctx the parse tree
	 */
	void enterTerm2(SimpleParser.Term2Context ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleParser#term2}.
	 * @param ctx the parse tree
	 */
	void exitTerm2(SimpleParser.Term2Context ctx);
}