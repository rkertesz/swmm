//-----------------------------------------------------------------------------
// 	  This file is part of a modified version of EPA SWMM called ecSWMM with RPN 
//    (reverse polish notation) control rules.
//
//    ecSWMM is provided as free software: under the terms of the BSD free 
//    software license included in the file repository. 
//	  
//    Authors: Fred Meyers, Ruben Kertesz, EmNet, LLC. <github @ emnet.net>
//
//	  Portions of this software have not been changed from the original
//	  source provided to public domain by EPA SWMM.
//
//-----------------------------------------------------------------------------
//    ecSWMM 5.1.010
//-----------------------------------------------------------------------------
//   controls.c
//
// BASED OFF OF HEAD RELEASE at OpenWaterAnalytics
//             08/05/15 (Build 5.1.010)

//   Author:   L. Rossman
//
//   Rule-based controls functions.
//
//   Control rules have the format:
//     RULE name
//     IF <premise>
//     AND / OR <premise>
//     etc.
//     THEN <action>
//     AND  <action>
//     etc.
//     ELSE <action>
//     AND  <action>
//     etc.
//     PRIORITY <p>
//
//   <premise> consists of:
//      <variable> <relational operator> value / <variable>
//   where <variable> is <object type> <id name> <attribute>
//   E.g.: Node 123 Depth > 4.5
//         Node 456 Depth < Node 123 Depth
//
//   <action> consists of:
//      <variable> = setting
//   E.g.: Pump abc status = OFF
//         Weir xyz setting = 0.5
//
//  Build 5.1.008:
//  - Support added for r.h.s. variables in rule premises.
//  - Node volume added as a premise variable.
//
//  Build 5.1.009:
//  - Fixed problem with parsing a RHS premise variable.
//
//  Build 5.1.010:
//  - Support added for link TIMEOPEN & TIMECLOSED premises.
//
//-----------------------------------------------------------------------------
#define _CRT_SECURE_NO_DEPRECATE
#define MAX_STACK  1000			//2014-09-02:EMNET
#define BIG_NUMBER 1e32			//2014-09-04:EMNET
#define EPSILON    1e-20		//2014-09-04:EMNET
#include <string.h>
#include <malloc.h>
#include <math.h>
#include "headers.h"

//-----------------------------------------------------------------------------
//  Constants
//-----------------------------------------------------------------------------

enum RuleState   {r_RULE, r_IF, r_AND, r_OR, r_THEN, r_ELSE, r_PRIORITY,
                  r_ERROR};
enum RuleObject  {r_NODE, r_LINK, r_CONDUIT, r_PUMP, r_ORIFICE, r_WEIR,
	              r_OUTLET, r_SIMULATION, r_STACK};								//2014-08-28:EMNET: added r_STACK
enum RuleAttrib  {r_DEPTH, r_HEAD, r_VOLUME, r_INFLOW, r_FLOW, r_STATUS, r_SETTING,
                  r_TIMEOPEN, r_TIMECLOSED, r_TIME, r_DATE, 
				  r_CLOCKTIME, r_DAY, r_MONTH, r_STACK_RESULT, r_STACK_OPER};			//2014-08-28:EMNET: added r_STACK_RESULT, r_STACK_OPER
//enum RuleRelation {EQ, NE, LT, LE, GT, GE}; Removed from head build and replaced with below // EMNET RK 2015-09-08
enum RuleRelation {EQ, NE, LT, LE, GT, GE, 
				Stack_Enter, Stack_Pop, Stack_Add, Stack_Subtract, Stack_Multiply, Stack_Divide, Stack_Expo, Stack_Invert,
				Stack_ChangeSign, Stack_Swap, Stack_LOG10, Stack_LN, Stack_EXP, Stack_SQRT,
				Stack_SIN, Stack_COS, Stack_TAN, Stack_ASIN, Stack_ACOS, Stack_ATAN,					
				Stack_Equal, Stack_NotEqual, Stack_Greater, Stack_GreaterEqual, Stack_LessThan, Stack_LessThanEqual,
				Stack_Back};		//2014-08-28:EMNET: added Stack Operands

/// SEE BELOW!!!!!!!!!! --------------- enum RuleSetting { r_CURVE, r_TIMESERIES, r_PID, r_PID2, r_PID3, r_STACKRESULT_ACTION, r_NUMERIC };			//2014-08-28L added r_STACKRESULT_ACTION;  2014-09-10:r_PID2, r_PID3

//2014-10-15:EMNET: the logic that uses Attributes gets confused in some cases of a RuleAttib having the same value as a RuleSetting.
//Rather than track down all the instances of logic problems, just bump the RuleSetting values up by 100 to keep them separate.  Nothing really uses the enum directly.
//2015-10-15:This has been made likely unnecessary by the LHS <relation> RHS rule structure, however it shall remain until thoroughly proven unnecessary 
/*
const int r_CURVE = 100;
const int r_TIMESERIES = 101;
const int r_PID = 102;
const int r_PID2 = 103;						//2014-09-10:EMNET
const int r_PID3 = 104;						//2014-09-10:EMNET
const int r_STACKRESULT_ACTION = 105;		//2014-08-28:EMNET
const int r_NUMERIC = 106;
*/
//The above used to use const int but this throws a fit using GCC compiler. Changed to close reported issue. ///RK
#define r_CURVE 100
#define r_TIMESERIES 101
#define r_PID 102
#define r_PID2 103						//2014-09-10:EMNET
#define r_PID3 104						//2014-09-10:EMNET
#define r_STACKRESULT_ACTION 105		//2014-08-28:EMNET
#define r_NUMERIC 106

static char* ObjectWords[] =
    {"NODE", "LINK", "CONDUIT", "PUMP", "ORIFICE", "WEIR", "OUTLET",
	 "SIMULATION", "STACK", NULL};
	 
static char* AttribWords[] =
    {"DEPTH", "HEAD", "VOLUME", "INFLOW", "FLOW", "STATUS", "SETTING",         //(5.1.008)
     "TIMEOPEN", "TIMECLOSED","TIME", "DATE", "CLOCKTIME", "DAY", "MONTH",     //(5.1.010)
     "RESULT", "OP", NULL}; //2014-08-28:EMNET: aded RESULT and OP for STACK object
	 
static char* RelOpWords[] = {"=", "<>", "<", "<=", ">", ">=", //NULL}; // ///RK comment 9/13/2015. Many in list were taken from 5.1.007 operand word list
"[ENTER]", "[POP]", "[+]", "[-]", "[*]", "[/]", "[y^x]", "[1/x]",
"[CHS]", "[SWAP]", "[LOG10]", "[LN]", "[EXP]", "[SQRT]", "[SIN]", "[COS]", "[TAN]", "[ASIN]", "[ACOS]", "[ATAN]",
"[X=Y]", "[X<>Y]", "[X>Y]", "[X>=Y]", "[X<Y]", "[X<=Y]", "[BACK]", NULL };

static char* StatusWords[]  = {"OFF", "ON", NULL};
static char* ConduitWords[] = {"CLOSED", "OPEN", NULL};
static char* SettingTypeWords[] = { "CURVE", "TIMESERIES", "PID", "PID2", "PID3", "STACK", NULL };		//2014-09-04:EMNET: added STACK RESULT as a SETTING type;  2014-09-10:PID2, PID3

//-----------------------------------------------------------------------------                  
// Data Structures
//-----------------------------------------------------------------------------
// Rule Premise Variable
struct TVariable
{
   int      node;            // index of a node (-1 if N/A)
   int      link;            // index of a link (-1 if N/A)
   int      attribute;       // type of attribute for node/link
};

// Rule Premise Clause 
struct  TPremise
{
    int     type;                 // clause type (IF/AND/OR)
    struct  TVariable lhsVar;     // left hand side variable                   //(5.1.008)
    struct  TVariable rhsVar;     // right hand side variable                  //(5.1.008)
    int     relation;             // relational operator (>, <, =, etc)
    double  value;                // right hand side value
    struct  TPremise *next;       // next premise clause of rule
};

// Rule Action Clause
struct  TAction              
{
   int     rule;             // index of rule that action belongs to
   int     link;             // index of link being controlled
   int     attribute;        // attribute of link being controlled
   int     curve;            // index of curve for modulated control
   int     tseries;          // index of time series for modulated control
   double  value;            // control setting for link attribute
   double  kp, ki, kd;       // coeffs. for PID modulated control
   double  e1, e2, e3;           // PID set point error from previous time steps //2014-09-23:EMNET: added e3 for the PID3 derivative term
   struct  TAction *next;    // next action clause of rule
};

// List of Control Actions
struct  TActionList          
{
   struct  TAction* action;
   struct  TActionList* next;
};

// Control Rule
struct  TRule
{
   char*    ID;                        // rule ID
   double   priority;                  // priority level
   struct   TPremise* firstPremise;    // pointer to first premise of rule
   struct   TPremise* lastPremise;     // pointer to last premise of rule
   struct   TAction*  thenActions;     // linked list of actions if true
   struct   TAction*  elseActions;     // linked list of actions if false
};

//-----------------------------------------------------------------------------
//  Shared variables
//-----------------------------------------------------------------------------
struct   TRule*       Rules;           // array of control rules
struct   TActionList* ActionList;      // linked list of control actions
int      InputState;                   // state of rule interpreter
int      RuleCount;                    // total number of rules
double   ControlValue;                 // value of controller variable
double   SetPoint;                     // value of controller setpoint
DateTime CurrentDate;                  // current date in whole days 
DateTime CurrentTime;                  // current time of day (decimal)
DateTime ElapsedTime;                  // elasped simulation time (decimal days)

double Control_Stack[MAX_STACK] = { NAN };		//2014-09-02: EMNET CONTROL STACK VALUES
int    Stack_Index;	      						//2014-09-02: EMNET CONTROL STACK INDEX: increments UP from 0


//-----------------------------------------------------------------------------
//2014-09-11:EMNET: copied from report.c for the new stack_back function
//  Imported variables
//-----------------------------------------------------------------------------
#define REAL4 float
extern REAL4* SubcatchResults;         // Results vectors defined in OUTPUT.C
extern REAL4* NodeResults;             //  "
extern REAL4* LinkResults;             //  " 



//-----------------------------------------------------------------------------
//  External functions (declared in funcs.h)
//-----------------------------------------------------------------------------
//     controls_create
//     controls_delete
//     controls_addRuleClause
//     controls_evaluate

//-----------------------------------------------------------------------------
//  Local functions
//-----------------------------------------------------------------------------


int checkValue(struct TPremise* p, double x);
int    addPremise(int r, int type, char* Tok[], int nToks);
int    getPremiseVariable(char* tok[], int* k, struct TVariable* v);
int    getPremiseValue(char* token, int attrib, double* value);
int    addAction(int r, char* Tok[], int nToks);

int    evaluatePremise(struct TPremise* p, double tStep);
double getVariableValue(struct TVariable v);
int    compareTimes(double lhsValue, int relation, double rhsValue,
       double halfStep);
int    compareValues(double lhsValue, int relation, double rhsValue);

void   updateActionList(struct TAction* a);
int    executeActionList(DateTime currentTime);
void   clearActionList(void);
void   deleteActionList(void);
void   deleteRules(void);

int    findExactMatch(char *s, char *keyword[]);
int    setActionSetting(char* tok[], int nToks, int* curve, int* tseries,
       int* attrib, double* value);
void   updateActionValue(struct TAction* a, DateTime currentTime, double dt);
double getPIDSetting(struct TAction* a, double dt);

double getPID2_Setting(struct TAction* a, double dt);
double getPID3_Setting(struct TAction* a, double dt);

void Stack_Push(double TopValue);
double Stack_Pop_value();
void Clear_Stack();
double Fetch_Stack_Operand(struct TPremise* p);


//=============================================================================

int  controls_create(int n)
//
//  Input:   n = total number of control rules
//  Output:  returns error code
//  Purpose: creates an array of control rules.
//
{
   int r;
   ActionList = NULL;
   InputState = r_PRIORITY;
   RuleCount = n;
   if ( n == 0 ) return 0;
   Rules = (struct TRule *) calloc(RuleCount, sizeof(struct TRule));
   if (Rules == NULL) return ERR_MEMORY;
   for ( r=0; r<RuleCount; r++ )
   {
       Rules[r].ID = NULL;
       Rules[r].firstPremise = NULL;
       Rules[r].lastPremise = NULL;
       Rules[r].thenActions = NULL;
       Rules[r].elseActions = NULL;
       Rules[r].priority = 0.0;    
   }
   return 0;
}

//=============================================================================

void controls_delete(void)
//
//  Input:   none
//  Output:  none
//  Purpose: deletes all control rules.
//
{
   if ( RuleCount == 0 ) return;
   deleteActionList();
   deleteRules();
}

//=============================================================================

int  controls_addRuleClause(int r, int keyword, char* tok[], int nToks)
//
//  Input:   r = rule index
//           keyword = the clause's keyword code (IF, THEN, etc.)
//           tok = an array of string tokens that comprises the clause
//           nToks = number of tokens
//  Output:  returns an error  code
//  Purpose: addd a new clause to a control rule.
//
{
    switch (keyword)
    {
      case r_RULE:
        if ( Rules[r].ID == NULL )
            Rules[r].ID = project_findID(CONTROL, tok[1]);
        InputState = r_RULE;
        if ( nToks > 2 ) return ERR_RULE;
        return 0;

      case r_IF:
        if ( InputState != r_RULE ) return ERR_RULE;
        InputState = r_IF;
        return addPremise(r, r_AND, tok, nToks);

      case r_AND:
        if ( InputState == r_IF ) return addPremise(r, r_AND, tok, nToks);
        else if ( InputState == r_THEN || InputState == r_ELSE )
            return addAction(r, tok, nToks);
        else return ERR_RULE;

      case r_OR:
        if ( InputState != r_IF ) return ERR_RULE;
        return addPremise(r, r_OR, tok, nToks);

      case r_THEN:
        if ( InputState != r_IF ) return ERR_RULE;
        InputState = r_THEN;
        return addAction(r, tok, nToks);

      case r_ELSE:
        if ( InputState != r_THEN ) return ERR_RULE;
        InputState = r_ELSE;
        return addAction(r, tok, nToks);

      case r_PRIORITY:
        if ( InputState != r_THEN && InputState != r_ELSE ) return ERR_RULE;
        InputState = r_PRIORITY;
        if ( !getDouble(tok[1], &Rules[r].priority) ) return ERR_NUMBER;
        if ( nToks > 2 ) return ERR_RULE;
        return 0;
    }
    return 0;
}

//=============================================================================

int controls_evaluate(DateTime currentTime, DateTime elapsedTime, double tStep)
//
//  Input:   currentTime = current simulation date/time
//           elapsedTime = decimal days since start of simulation
//           tStep = simulation time step (days)
//  Output:  returns number of new actions taken
//  Purpose: evaluates all control rules at current time of the simulation.
//
{
    int    r;                          // control rule index
    static int    result;                     // TRUE if rule premises satisfied
    struct TPremise* p;                // pointer to rule premise clause
    struct TAction*  a;                // pointer to rule action clause

    // --- save date and time to shared variables
    CurrentDate = floor(currentTime);
    CurrentTime = currentTime - floor(currentTime);
    ElapsedTime = elapsedTime;

    // --- evaluate each rule
    if ( RuleCount == 0 ) return 0;
    clearActionList();

	Clear_Stack();			//2014-09-02:EMNET

    for (r=0; r<RuleCount; r++)
    {
        // --- evaluate rule's premises
        result = TRUE;
        p = Rules[r].firstPremise;
        while (p)
        {
            if ( p->type == r_OR )
            {
                if ( result == FALSE )
                    result = evaluatePremise(p, tStep);
            }
            else
            {
                if ( result == FALSE ) break;  // and condition ///RK - ideally rule results and premis results separate var
                result = evaluatePremise(p, tStep);
            }
            p = p->next;
        }    

        // --- if premises true, add THEN clauses to action list
        //     else add ELSE clauses to action list
        if ( result == TRUE ) a = Rules[r].thenActions;
        else                  a = Rules[r].elseActions;
        while (a)
        {
            updateActionValue(a, currentTime, tStep);
            updateActionList(a);
            a = a->next;
        }
    }

    // --- execute actions on action list
    if ( ActionList ) return executeActionList(currentTime);
    else return 0;
}

//=============================================================================

//  This function was revised to add support for r.h.s. premise variables. //  //(5.1.008)

int  addPremise(int r, int type, char* tok[], int nToks)
//
//  Input:   r = control rule index
//           type = type of premise (IF, AND, OR)
//           tok = array of string tokens containing premise statement
//           nToks = number of string tokens
//  Output:  returns an error code
//  Purpose: adds a new premise to a control rule.
//
{	
    int    relation, n, err = 0;
    double value = MISSING;
    struct TPremise* p;
    struct TVariable v1;
    struct TVariable v2;
	int    obj; // 2015-9-8 RK EMNET added back in to get correct number of tokens depending on if we are using stack or not

//	if (nToks < 5) return ERR_ITEMS;	// original 5.1.010 code
	 // --- make sure there is at least 1 token ---- 2014-09-04:EMNET
	if (nToks < 1) return ERR_ITEMS;	// ---- 2014-09-04:EMNET
	obj = findExactMatch(tok[1], ObjectWords);			//2014-08-13:EMNET: this was just findmatch() before 
	if (obj < 0) return error_setInpError(ERR_KEYWORD, tok[1]); // EMNET 2015-9-13
	if (obj != r_STACK)		//2014-09-04:EMNET
		if (nToks < 5) return ERR_ITEMS;

    // --- get LHS variable /// Why isn't v1 initialized with parameters (in original 5.1.010 code)? ///RK 10-9-15
    n = 1;
    err = getPremiseVariable(tok, &n, &v1);
    if ( err > 0 ) return err;

    // --- get relational operator
    n++;
    relation = findExactMatch(tok[n], RelOpWords);
    if ( relation < 0 ) return error_setInpError(ERR_KEYWORD, tok[n]);
    n++;

	
    // --- initialize RHS variable
    v2.attribute = -1;
    v2.link = -1;
    v2.node = -1;

    // --- check that more tokens remain
    if ( n >= nToks ) return error_setInpError(ERR_ITEMS, "");
		
  
	if (_stricmp(tok[n], "---") == 0) {		//2014-09-04:EMNET: allow for possibly "empty" stack value
		value = 0.0;						//2014-09-04:EMNET: just to give it some value (will not be used anywhere)
	}
	// --- otherwise get value to which LHS variable is compared to
	else	{
		// --- see if a RHS variable is supplied
		  if ( findmatch(tok[n], ObjectWords) >= 0 && n + 3 >= nToks )  
		//  looks like stich case for Date, Day, etc... ///RK 
		 {
			err = getPremiseVariable(tok, &n, &v2);
			if ( err > 0 ) return ERR_RULE;                                        //(5.1.009)
			if ( v1.attribute != v2.attribute)                                     //(5.1.009)
				report_writeWarningMsg(WARN11, Rules[r].ID);                       //(5.1.009)
		}

        err = getPremiseValue(tok[n], v1.attribute, &value);
        n++;
    }
    if ( err > 0 ) return err;

    // --- make sure another clause is not on same line
    //if ( n < nToks && findmatch(tok[n], RuleKeyWords) >= 0 ) return ERR_RULE; // original 5.1.010 code
	if (n < nToks && findExactMatch(tok[n], RuleKeyWords) >= 0) return ERR_RULE;			//2014-08-13:EMNET: this was just findmatch() before

    // --- create the premise object
    p = (struct TPremise *) malloc(sizeof(struct TPremise));
    if ( !p ) return ERR_MEMORY;
    p->type      = type;
    p->lhsVar    = v1;
    p->rhsVar    = v2;
    p->relation  = relation;
    p->value     = value;
    p->next      = NULL;
    if ( Rules[r].firstPremise == NULL )
    {
        Rules[r].firstPremise = p;
    }
    else
    {
        Rules[r].lastPremise->next = p;
    }
    Rules[r].lastPremise = p;
    return 0;
}
	
	
	


//=============================================================================

int getPremiseVariable(char* tok[], int* k, struct TVariable* v)
//
//  Input:   tok = array of string tokens containing premise statement
//           k = index of current token
//  Output:  returns an error code; updates k to new current token and
//           places identity of specified variable in v
//  Purpose: parses a variable (e.g., Node 123 Depth) specified in a
//           premise clause of a control rule.
//
{
    int    n = *k;
    int    node = -1;
    int    link = -1;
    int    obj, attrib;

    // --- get object type
    //obj = findmatch(tok[n], ObjectWords);
	obj = findExactMatch(tok[n], ObjectWords);			//2014-08-13:EMNET: this was just findmatch() before // Revised [1] to [n] 2015-9-8 RK
    if ( obj < 0 ) return error_setInpError(ERR_KEYWORD, tok[n]);

    // --- get object index from its name
    n++;
    switch (obj)
    {
      case r_NODE:
        node = project_findObject(NODE, tok[n]);
        if ( node < 0 ) return error_setInpError(ERR_NAME, tok[n]);
        break;

      case r_LINK:
      case r_CONDUIT:
      case r_PUMP:
      case r_ORIFICE:
      case r_WEIR:
      case r_OUTLET:
        link = project_findObject(LINK, tok[n]);
        if ( link < 0 ) return error_setInpError(ERR_NAME, tok[n]);
        break;
		
	  case r_SIMULATION:		//2014-08-14:EMNET (was simply handled as default case before)
	  case r_STACK:			//2014-08-28:EMNET
	  //default: n = 1;			//since there is no NAME following SIMULATION or STACK, as there is with NODE or LINK, etc.
      // break;   
      default: n--;
    }
    n++;

    // --- get attribute index from its name
    //attrib = findmatch(tok[n], AttribWords);
	attrib = findExactMatch(tok[n], AttribWords);			//2014-08-13:EMNET: this was just findmatch() before
    if ( attrib < 0 ) return error_setInpError(ERR_KEYWORD, tok[n]);

    // --- check that attribute belongs to object type
    if ( obj == r_NODE ) switch (attrib)
    {
      case r_DEPTH:
      case r_HEAD:
      case r_VOLUME:                                                           //(5.1.008)
      case r_INFLOW: break;
      default: return error_setInpError(ERR_KEYWORD, tok[n]);
    }

////  Added to release 5.1.010.  ////                                          //(5.1.010)
    // --- check for link TIMEOPEN & TIMECLOSED attributes
    else if ( link >= 0  &&
            ( (attrib == r_TIMEOPEN ||
               attrib == r_TIMECLOSED)
            ))
    {
 
    }
////

    else if ( obj == r_LINK || obj == r_CONDUIT ) switch (attrib)
    {
      case r_STATUS:
      case r_DEPTH:
      case r_FLOW: break;
      default: return error_setInpError(ERR_KEYWORD, tok[n]);
    }
    else if ( obj == r_PUMP ) switch (attrib)
    {
      case r_FLOW:
      case r_STATUS: break;
      default: return error_setInpError(ERR_KEYWORD, tok[n]);
    }
    else if ( obj == r_ORIFICE || obj == r_WEIR ||
              obj == r_OUTLET ) switch (attrib)
    {
      case r_SETTING: break;
      default: return error_setInpError(ERR_KEYWORD, tok[n]);
    }
    else switch (attrib)
    {
      case r_TIME:
      case r_DATE:
      case r_CLOCKTIME:
      case r_DAY:
      case r_MONTH: break;
	  case r_STACK_RESULT: break;				//2014-08-28:EMNET
	  case r_STACK_OPER:   break;				//2014-09-03:EMNET
      default: return error_setInpError(ERR_KEYWORD, tok[n]);
    }

    // --- populate variable structure
    v->node      = node;
    v->link      = link;
    v->attribute = attrib;
    *k = n;
    return 0;
}

//=============================================================================

int getPremiseValue(char* token, int attrib, double* value)
//
//  Input:   token = a string token
//           attrib = index of a node/link attribute
//  Output:  value = attribute value;
//           returns an error code;
//  Purpose: parses the numerical value of a particular node/link attribute
//           in the premise clause of a control rule.
//
{
    switch (attrib)
    {
      case r_STATUS:
        *value = findmatch(token, StatusWords);
		if ( *value < 0.0 ) *value = findmatch(token, ConduitWords);
        if ( *value < 0.0 ) return error_setInpError(ERR_KEYWORD, token);
        break;

      case r_TIME:
      case r_CLOCKTIME:
      case r_TIMEOPEN:                                                         //(5.1.010)
      case r_TIMECLOSED:                                                       //(5.1.010)
        if ( !datetime_strToTime(token, value) )
            return error_setInpError(ERR_DATETIME, token);
        break;

      case r_DATE:
        if ( !datetime_strToDate(token, value) )
            return error_setInpError(ERR_DATETIME, token);
        break;

      case r_DAY:
        if ( !getDouble(token, value) ) 
            return error_setInpError(ERR_NUMBER, token);
        if ( *value < 1.0 || *value > 7.0 )
             return error_setInpError(ERR_DATETIME, token);
        break;

      case r_MONTH:
        if ( !getDouble(token, value) )
            return error_setInpError(ERR_NUMBER, token);
        if ( *value < 1.0 || *value > 12.0 )
             return error_setInpError(ERR_DATETIME, token);
        break;
       
      default: if ( !getDouble(token, value) )
          return error_setInpError(ERR_NUMBER, token);
    }
    return 0;
}

//=============================================================================

int  addAction(int r, char* tok[], int nToks)
//
//  Input:   r = control rule index
//           tok = array of string tokens containing action statement
//           nToks = number of string tokens
//  Output:  returns an error code
//  Purpose: adds a new action to a control rule.
//
{
    int    obj, link, attrib;
    int    curve = -1, tseries = -1;
    int    n;
    int    err;
    double values[] = {1.0, 0.0, 0.0};

    struct TAction* a;

    // --- check for proper number of tokens
    if ( nToks < 6 ) return error_setInpError(ERR_ITEMS, "");

    // --- check for valid object type
	obj = findExactMatch(tok[1], ObjectWords);									//2014-08-13:EMNET: this was just findmatch() before
    if ( obj != r_LINK && obj != r_CONDUIT && obj != r_PUMP && 
		obj != r_ORIFICE && obj != r_WEIR && obj != r_OUTLET)		
        return error_setInpError(ERR_KEYWORD, tok[1]);

    // --- check that object name exists and is of correct type
    link = project_findObject(LINK, tok[2]);
    if ( link < 0 ) return error_setInpError(ERR_NAME, tok[2]);
    switch (obj)
    {
      case r_CONDUIT:
	if ( Link[link].type != CONDUIT )
	    return error_setInpError(ERR_NAME, tok[2]);
	break;
      case r_PUMP:
        if ( Link[link].type != PUMP )
            return error_setInpError(ERR_NAME, tok[2]);
        break;
      case r_ORIFICE:
        if ( Link[link].type != ORIFICE )
            return error_setInpError(ERR_NAME, tok[2]);
        break;
      case r_WEIR:
        if ( Link[link].type != WEIR )
            return error_setInpError(ERR_NAME, tok[2]);
        break;
      case r_OUTLET:
        if ( Link[link].type != OUTLET )
            return error_setInpError(ERR_NAME, tok[2]);
		break;
    }

    // --- check for valid attribute name
	attrib = findExactMatch(tok[3], AttribWords);			//2014-08-13:EMNET: this was just findmatch() before
    if ( attrib < 0 ) return error_setInpError(ERR_KEYWORD, tok[3]);

    // --- get control action setting
    if ( obj == r_CONDUIT )
    {
        if ( attrib == r_STATUS )
	{
			values[0] = findExactMatch(tok[5], ConduitWords);			//2014-08-13:EMNET: this was just findmatch() before
            if ( values[0] < 0.0 )
                return error_setInpError(ERR_KEYWORD, tok[5]);
        }
        else return error_setInpError(ERR_KEYWORD, tok[3]);
    }

    else if ( obj == r_PUMP )
    {
        if ( attrib == r_STATUS )
        {
			values[0] = findExactMatch(tok[5], StatusWords);			//2014-08-13:EMNET: this was just findmatch() before
            if ( values[0] < 0.0 )
                return error_setInpError(ERR_KEYWORD, tok[5]);
        }
        else if ( attrib == r_SETTING )
        {
            err = setActionSetting(tok, nToks, &curve, &tseries,
                                   &attrib, values);
            if ( err > 0 ) return err;
        }
        else return error_setInpError(ERR_KEYWORD, tok[3]);
    }

    else if ( obj == r_ORIFICE || obj == r_WEIR || obj == r_OUTLET )
    {
        if ( attrib == r_SETTING )
        {
           err = setActionSetting(tok, nToks, &curve, &tseries,
                                  &attrib, values);
           if ( err > 0 ) return err;
           if (  attrib == r_SETTING
           && (values[0] < 0.0 || values[0] > 1.0) ) 
               return error_setInpError(ERR_NUMBER, tok[5]);
        }
        else return error_setInpError(ERR_KEYWORD, tok[3]);
    }
    else return error_setInpError(ERR_KEYWORD, tok[1]);

    // --- check if another clause is on same line
    n = 6;
    if ( curve >= 0 || tseries >= 0 ) n = 7;
	if ((attrib == r_PID) || (attrib == r_PID2) || (attrib == r_PID3)) n = 9;			//2014-09-10:EMNET: added  || (attrib == r_PID2) ... and r_PID3 
	if (n < nToks && findExactMatch(tok[n], RuleKeyWords) >= 0) return ERR_RULE;			//2014-08-13:EMNET: this was just findmatch() before

    // --- create the action object
    a = (struct TAction *) malloc(sizeof(struct TAction));
    if ( !a ) return ERR_MEMORY;
    a->rule      = r;
    a->link      = link;
    a->attribute = attrib;
    a->curve     = curve;
    a->tseries   = tseries;
    a->value     = values[0];
	if ((attrib == r_PID) || (attrib == r_PID2) || (attrib == r_PID3))			//2014-09-10:EMNET: added  || (attrib == r_PID2) ... and r_PID3
    {
        a->kp = values[0];
        a->ki = values[1];
        a->kd = values[2];
        a->e1 = 0.0;
        a->e2 = 0.0;
		a->e3 = 0.0;		//2014-09-23:EMNET: for PID3 function
    }
    if ( InputState == r_THEN )
    {
        a->next = Rules[r].thenActions;
        Rules[r].thenActions = a;
    }
    else
    {
        a->next = Rules[r].elseActions;
        Rules[r].elseActions = a;
    }
    return 0;
}

//=============================================================================

int  setActionSetting(char* tok[], int nToks, int* curve, int* tseries,
                      int* attrib, double values[])
//
//  Input:   tok = array of string tokens containing action statement
//           nToks = number of string tokens
//  Output:  curve = index of controller curve
//           tseries = index of controller time series
//           attrib = r_PID if PID controller used  -- 2014-09-04:EMNET: or r_PID2 or r_PID3
//           values = values of control settings
//           returns an error code
//  Purpose: identifies how control actions settings are determined.
//
{
    int k, m;

    // --- see if control action is determined by a Curve or Time Series
    if (nToks < 6) return error_setInpError(ERR_ITEMS, "");
	k = findExactMatch(tok[5], SettingTypeWords);			//2014-08-13:EMNET: this was just findmatch() before
    if ( k >= 0 && nToks < 7 ) return error_setInpError(ERR_ITEMS, "");

	k += 100;		//2014-10-15:EMNET: for new +100 list of ACTION RULE SETTINGS
    
	switch (k)
    {

    // --- control determined by a curve - find curve index
    case r_CURVE:
        m = project_findObject(CURVE, tok[6]);
        if ( m < 0 ) return error_setInpError(ERR_NAME, tok[6]);
        *curve = m;
        break;

    // --- control determined by a time series - find time series index
    case r_TIMESERIES:
        m = project_findObject(TSERIES, tok[6]);
        if ( m < 0 ) return error_setInpError(ERR_NAME, tok[6]);
        *tseries = m;
        Tseries[m].refersTo = CONTROL;
        break;

    // --- control determined by PID controller 
    case r_PID:
	case r_PID2:
	case r_PID3:
		if (nToks < 9) return error_setInpError(ERR_ITEMS, "");
        for (m=6; m<=8; m++)
        {
            if ( !getDouble(tok[m], &values[m-6]) )
                return error_setInpError(ERR_NUMBER, tok[m]);
        }

		//2014-10-15:EMNET: NOTE: EPA line of code below replaces what was an "R_SETTING" code by "R_PID".  
		//But that ends up using one of the "RuleSetting" codes instead of one from the "RuleAttrib" list, 
		//and that led to cross-over problems when the lists were updated with new commands.
		//And that is why all the RuleSetting codes are +100 now -- to avoid those conflicts in evaluatePremise();
		//2015-10-14 This needs to be evaluated to determine if it remains an issue given the refactoring of official SWMM code in version 5.1.010 ///RK

		*attrib = k;			//2014-09-10:EMNET: r_PID  or r_PID2  or r_PID3
        break;

	case r_STACKRESULT_ACTION:
		///   *attrib = r_STACKRESULT_ACTION;			//2014-09-04:EMNET
		///   attrib is only for the item on the LEFT of the equal sign.
		//2014-10-10: NEW WAY OF MARKING "STACK RESULT" on the right side of equal sign in an Action:
		*curve = -999;
		*tseries = -999;
		break;

    // --- direct numerical control is used
    default:
        if ( !getDouble(tok[5], &values[0]) )
            return error_setInpError(ERR_NUMBER, tok[5]);
    }
    return 0;
}

//=============================================================================

void  updateActionValue(struct TAction* a, DateTime currentTime, double dt)
//
//  Input:   a = an action object
//           currentTime = current simulation date/time (days)
//           dt = time step (days)
//  Output:  none
//  Purpose: updates value of actions found from Curves or Time Series.
//
{
    if ( a->curve >= 0 )
    {
        a->value = table_lookup(&Curve[a->curve], ControlValue);
    }
    else if ( a->tseries >= 0 )
    {
        a->value = table_tseriesLookup(&Tseries[a->tseries], currentTime, TRUE);
    }
    else if ( a->attribute == r_PID )
    {
        a->value = getPIDSetting(a, dt);
    }
	else if (a->attribute == r_PID2)			//2014-09-10:EMNET
	{
		a->value = getPID2_Setting(a, dt);		//2014-09-10:EMNET
	}
	else if (a->attribute == r_PID3)			//2014-09-23:EMNET
	{
		a->value = getPID3_Setting(a, dt);		//2014-09-23:EMNET
	}


	else if ((a->curve == -999) && (a->tseries == -999)) {			//2014-10-10: new way of flagging r_STACKRESULT_ACTION
		if ((Stack_Index >= 0) && (Stack_Index < MAX_STACK))
			a->value = Control_Stack[Stack_Index];		//2014-09-04:EMNET: Use TOP-of-STACK value in the ACTION
		else
			a->value = 0.0;
	}
}

//=============================================================================

double getPIDSetting(struct TAction* a, double dt)
//
//  Input:   a = an action object
//           dt = current time step (days)
//  Output:  returns a new link setting 
//  Purpose: computes a new setting for a link subject to a PID controller.
//
//  Note:    a->kp = gain coefficient,
//           a->ki = integral time (minutes)
//           a->k2 = derivative time (minutes)
//           a->e1 = error from previous time step
//           a->e2 = error from two time steps ago
{
    double e0, setting;
	double p, i, d, update;
	double tolerance = 0.0001;

	// --- convert time step from days to minutes
	dt *= 1440.0;

    // --- determine relative error in achieving controller set point
    e0 = SetPoint - ControlValue;
    if ( fabs(e0) > TINY )
    {
        if ( SetPoint != 0.0 ) e0 = e0/SetPoint;
        else                   e0 = e0/ControlValue;
    }

	// --- reset previous errors to 0 if controller gets stuck
	if (fabs(e0 - a->e1) < tolerance)
	{
		a->e2 = 0.0;
		a->e1 = 0.0;
	}

    // --- use the recursive form of the PID controller equation to
    //     determine the new setting for the controlled link
	p = (e0 - a->e1);
	if ( a->ki == 0.0 ) i = 0.0;
	else i = e0 * dt / a->ki;
	d = a->kd * (e0 - 2.0*a->e1 + a->e2) / dt;
	update = a->kp * (p + i + d);
	if ( fabs(update) < tolerance ) update = 0.0;
	setting = Link[a->link].targetSetting + update;

	// --- update previous errors
    a->e2 = a->e1;
    a->e1 = e0;

    // --- check that new setting lies within feasible limits
    if ( setting < 0.0 ) setting = 0.0;
    if (Link[a->link].type != PUMP && setting > 1.0 ) setting = 1.0;
    return setting;
}

//=============================================================================
//=============================================================================
//=============================================================================
//=============================================================================
//
// 2014-09-10:EMNET ... special PID function, with KP applied to only the Proportional Term
//
double getPID2_Setting(struct TAction* a, double dt)
//
//  Input:   a = an action object
//           dt = current time step (days)
//  Output:  returns a new link setting 
//  Purpose: computes a new setting for a link subject to a PID controller.
//
//  Note:    a->kp = gain coefficient,
//           a->ki = integral time (minutes)
//           a->k2 = derivative time (minutes)
//           a->e1 = error from previous time step
//           a->e2 = error from two time steps ago
{
	double e0, setting;
	double p, i, d, update;
	double tolerance = 0.0001;

	// --- convert time step from days to minutes
	dt *= 1440.0;

	// --- determine relative error in achieving controller set point
	e0 = SetPoint - ControlValue;
	if (fabs(e0) > TINY)
	{
		if (SetPoint != 0.0) e0 = e0 / SetPoint;
		else                   e0 = e0 / ControlValue;
	}

	// --- reset previous errors to 0 if controller gets stuck
	if (fabs(e0 - a->e1) < tolerance)
	{
		a->e2 = 0.0;
		a->e1 = 0.0;
	}

	// --- use the recursive form of the PID controller equation to
	//     determine the new setting for the controlled link
	p = (e0 - a->e1);
	if (a->ki == 0.0) i = 0.0;
	else i = e0 * dt / a->ki;
	d = a->kd * (e0 - 2.0*a->e1 + a->e2) / dt;
	//2014-09-10:EMNET -- this was the standard EPA SWMM PID equation, the original getPID_Setting() function:
	/////////////////////update = a->kp * (p + i + d);
	update = (a->kp * p) + i + d;			//2014-09-10:EMNET -- PID2 equation, with KP multiplied only times the Proportional Term
	if (fabs(update) < tolerance) update = 0.0;
	setting = Link[a->link].targetSetting + update;

	// --- update previous errors
	a->e2 = a->e1;
	a->e1 = e0;

	// --- check that new setting lies within feasible limits
	if (setting < 0.0) setting = 0.0;
	if (Link[a->link].type != PUMP && setting > 1.0) setting = 1.0;
	return setting;
}




//
// 2014-09-23:EMNET ... special PID function, with KP applied to only the Proportional Term
//
double getPID3_Setting(struct TAction* a, double dt)
//
//  Input:   a = an action object
//           dt = current time step (days)
//  Output:  returns a new link setting 
//  Purpose: computes a new setting for a link subject to a PID controller.
//
//  Note:    a->kp = gain coefficient,
//           a->ki = integral time (minutes)
//           a->k2 = derivative time (minutes)
//           a->e1 = error from previous time step
//           a->e2 = error from two time steps ago
//           a->e3 = error from 3 time steps ago			//2014-09-23:EMNET
{
	double e0, setting;
	double p, i, d, update;
	double tolerance = 0.0001;

	// --- convert time step from days to minutes
	dt *= 1440.0;

	// --- determine relative error in achieving controller set point
	e0 = SetPoint - ControlValue;
	if (fabs(e0) > TINY)
	{
		if (SetPoint != 0.0) e0 = e0 / SetPoint;
		else                   e0 = e0 / ControlValue;
	}

	// --- reset previous errors to 0 if controller gets stuck
	if (fabs(e0 - a->e1) < tolerance)
	{
		a->e3 = 0.0;		//2014-09-10:EMNET
		a->e2 = 0.0;
		a->e1 = 0.0;
	}

	// --- use the recursive form of the PID controller equation to
	//     determine the new setting for the controlled link
	p = (e0 - a->e1);
	if (a->ki == 0.0) i = 0.0;
	else i = e0 * dt / a->ki;
	
	//2014-09-23:EMNET -- this was the standard EPA SWMM derivative term:
	/////////////////////d = a->kd * (e0 - 2.0*a->e1 + a->e2) / dt;

	d = a->kd * (e0 - ((3.0*a->e1) - (2.0*a->e2) - (1.0*a->e3))) / dt;		//2014-09-24:EmNet: triple-sample derivative filter

	//2014-09-10:EMNET -- this was the standard EPA SWMM PID equation, the original getPID_Setting() function:
	/////////////////////update = a->kp * (p + i + d);
	update = (a->kp * p) + i + d;			//2014-09-10:EMNET -- PID2 equation, with KP multiplied only times the Proportional Term
	if (fabs(update) < tolerance) update = 0.0;
	setting = Link[a->link].targetSetting + update;

	// --- update previous errors
	a->e3 = a->e2;				//2014-09-10:EMNET
	a->e2 = a->e1;
	a->e1 = e0;

	// --- check that new setting lies within feasible limits
	if (setting < 0.0) setting = 0.0;
	if (Link[a->link].type != PUMP && setting > 1.0) setting = 1.0;

	return setting;
}
//=============================================================================
//=============================================================================
//=============================================================================
//=============================================================================

void updateActionList(struct TAction* a)
//
//  Input:   a = an action object
//  Output:  none
//  Purpose: adds a new action to the list of actions to be taken.
//
{
	struct TActionList* listItem;
	struct TAction* a1;
	double priority = Rules[a->rule].priority;

	// --- check if link referred to in action is already listed
	listItem = ActionList;
	while (listItem)
	{
		a1 = listItem->action;
		if (!a1) break;
		if (a1->link == a->link)
		{
			// --- replace old action if new action has higher priority
			if (priority > Rules[a1->rule].priority) listItem->action = a;
			return;
		}
		listItem = listItem->next;
	}

	// --- action not listed so add it to ActionList
	if (!listItem)
	{
		listItem = (struct TActionList *) malloc(sizeof(struct TActionList));
		listItem->next = ActionList;
		ActionList = listItem;
	}
	listItem->action = a;
}

//=============================================================================

int executeActionList(DateTime currentTime)
//
//  Input:   currentTime = current date/time of the simulation
//  Output:  returns number of new actions taken
//  Purpose: executes all actions required by fired control rules.
//
{
	struct TActionList* listItem;
	struct TActionList* nextItem;
	struct TAction* a1;
	int count = 0;

	listItem = ActionList;
	while (listItem)
	{
		a1 = listItem->action;
		if (!a1) break;
		if (a1->link >= 0)
		{
			if (Link[a1->link].targetSetting != a1->value)
			{
				Link[a1->link].targetSetting = a1->value;
				if (RptFlags.controls)
					report_writeControlAction(currentTime, Link[a1->link].ID,
					a1->value, Rules[a1->rule].ID);
				count++;
			}
		}
		nextItem = listItem->next;
		listItem = nextItem;
	}
	return count;
}

//=============================================================================

/* <<<<<<< HEAD
int evaluatePremise(struct TPremise* p, DateTime theDate, DateTime theTime,

======= */

int evaluatePremise(struct TPremise* p, double tStep)
//
//  Input:   p = a control rule premise condition
//           tStep = current time step (days)
//  Output:  returns TRUE if the condition is true or FALSE otherwise
//  Purpose: evaluates the truth of a control rule premise condition.
//
{
    double lhsValue, rhsValue;
	
	/// Fred moved this above getvariablevalue to prevent its execution when dealing with stack result or stack op /// Clean up comments ///RK 10-14-15
	////Added by RK 10-9-15 because getVariableValue uses struct that is beneath TPremise, therefore incompatible with Value comparison
	switch (p->lhsVar.attribute)
	{
	case r_STACK_RESULT:
		return checkValue(p, Control_Stack[Stack_Index]);				//2014-09-02:EMNET: COMPARE premise value with current TOP-of-STACK -- or PERFORM STACK OPERATION

	case r_STACK_OPER:
		if (p->relation == Stack_Enter) {     //09-15-2015 EmNet Changed operand to relation //RK
			Stack_Push(p->value);				//2014-09-03:EMNET: PUSH new STACK VALUE onto the TOP-of-STACK
			return TRUE;
		}
		else {
			return checkValue(p, p->value);				//2014-09-02:EMNET: COMPARE premise value with current TOP-of-STACK -- or PERFORM STACK OPERATION
		}
	}
	/////Continue to check to see if we introduced a bug by not using evaluation of missing data as per getVariableValue END RK 10-9-15////

	////Original code 5.1.010 ///RK
	lhsValue = getVariableValue(p->lhsVar);
	if (p->value == MISSING) rhsValue = getVariableValue(p->rhsVar);         //(5.1.008)
	else                       rhsValue = p->value;                            //(5.1.008)
	if (lhsValue == MISSING || rhsValue == MISSING) return FALSE;

	//// Fred placed here to utilize result from getVariableValue ... We need lhsValue populated ///RK 10-14-15
	if (p->relation == Stack_Enter) {     //09-15-2015 EmNet Changed operand to relation //RK
		Stack_Push(lhsValue);				//2014-09-03:EMNET: PUSH new STACK VALUE onto the TOP-of-STACK
		return TRUE;
	}


	long Back_Steps; // EmNet Variable ///RK
	double back_value = 0.0;
	int myAttribute = p->lhsVar.attribute;//attribute;
//	DateTime myDateTime;
//	long numSeconds;
//	int hour, min, sec;
//	double myValue;

	
	
	
		//**********2014-09-11:EMNET: process [BACK] commands.********************
	if (p->relation == Stack_Back) {
		///RK changed operand to value

		//// ===========================================================================================================================
		//// TIME [BACK] will probably never be used, but here is working code A) to illustrate elapsed time manipulation and B) in case the function is needed someday.
		////Note that you really could accomplish the same thing by pushing SYSTEM TIME onto the stack then subtracting a decimal DateTime value.
		//if (myAttribute == r_TIME)	{
		//	if (elapsedTime > (p->value)) {			//	p->value for TIME is in decimal time format, coming from HH:MM:SS format on CONTROLS premise line
		//		//just compute the time; no reference to the output file:
		//		numSeconds = datetime_timeDiff(elapsedTime, (p->value));			//myDateTime becomes the decimal value of ELAPSED SIMULATION TIME,  [BACK] the specified amount
		//		myValue = ((double)numSeconds / (double)SECperDAY);
		//		Stack_Push(myValue);
		//		return TRUE;
		//	}
		//	else {
		//		return FALSE;
		//	}
		//}

		//// CLOCKTIME [BACK] will probably never be used, but here is working code A) to illustrate time-of-day manipulation and B) in case the function is needed someday:
		//if (myAttribute == r_CLOCKTIME) {
		//	//Must use REPORTSTEP -- not routing step! -- for [BACK] calculations, because only values at REPORT STEPS get recorded in the binary file.
		//	Back_Steps = (long)((((p->value * 24.0 * 60.0 * 60.0) / (double)ReportStep) + 0.5));     //because CLOCKTIME has a decimal DateTime p->value, not "number of seconds" like LINK and NODE premises
		//	if ((Back_Steps >= 0) && ((Nperiods - Back_Steps) > 0)) {
		//		output_readDateTime(Nperiods - Back_Steps, &myDateTime);	//myDateTime the decimal value of TIME-OF-DAY, [BACK] the specified amount from the current report step
		//		datetime_decodeTime(myDateTime, &hour, &min, &sec);			//year, month, day are IGNORED for CLOCKTIME
		//		myValue = ((double)((((hour * 60.0) + min) * 60.0) + sec)) / (double)SECperDAY;
		//		Stack_Push(myValue);
		//		return TRUE;
		//	}
		//	else {
		//		return FALSE;
		//	}
		//}
		//// ===========================================================================================================================
	

		//below is the code for the normal cases:   NODE [BACK] commands    and    LINK [BACK] commands:

		//Must use REPORTSTEP -- not routing step! -- for [BACK] calculations, because only values at REPORT STEPS get recorded in the binary file.
		Back_Steps = (long)(((p->value / (double)ReportStep)) + 0.5);		//9-23-2014: round [BACK] seconds-count to long integer Back_Steps

		//////***Used to be in the old controls added back by RK******
		/// Fred recommended moving to this location (within Stack_Back) to prevent confusion in upstream code ///RK
		/// Untested as of 10-14-2015 ///RK
		int i = p->lhsVar.node; // We probably need to remove this. Vestigial? ///RK 
		int j = p->lhsVar.link; 

		if ((Back_Steps >= 0) && ((Nperiods - Back_Steps) > 0)) {

			// NODE SECTION:

			if (i >= 0) {			// i = NODE subscript for requested node
				output_readNodeResults(Nperiods - Back_Steps, i);				//2014-09-11:EMNET: find value BACK N steps and PUSH onto the TOP-of-STACK

				if (myAttribute == r_DEPTH)  
					back_value = NodeResults[NODE_DEPTH];
				if (myAttribute == r_HEAD)  
					back_value = NodeResults[NODE_HEAD];
				if (myAttribute == r_INFLOW)  
					back_value = NodeResults[NODE_INFLOW];

				//Items below have values available in the NodeResults, but the standard EPA SWMM NODE command-line syntax only allows DEPTH, HEAD, and INFLOW
				// if (myAttribute == ????????)  back_value = NodeResults[NODE_VOLUME];
				// if (myAttribute == ????????)  back_value = NodeResults[NODE_LATFLOW];
				// if (myAttribute == ????????)  back_value = NodeResults[NODE_OVERFLOW];

			}
			
			// LINK and PUMP SECTION:

			else if (j >= 0) {			// j = LINK subscript for requested link ---- handles both LINK and PUMP premises:

				output_readLinkResults(Nperiods - Back_Steps, j);				//2014-09-11:EMNET: find value BACK N steps and PUSH onto the TOP-of-STACK

				if (myAttribute == r_FLOW)  
					back_value = LinkResults[LINK_FLOW];
				if (myAttribute == r_DEPTH)  
					back_value = LinkResults[LINK_DEPTH];

				//Items below have values available in the LinkResults, but the standard EPA SWMM NODE command-line syntax only allows DEPTH, HEAD, and INFLOW
				// if (myAttribute == ????????)  back_value = LinkResults[LINK_VELOCITY];
				// if (myAttribute == ????????)  back_value = LinkResults[LINK_VOLUME];
				// if (myAttribute == ????????)  back_value = LinkResults[LINK_CAPACITY];

				//PUMP STATUS ????   is STATUS even saved in the report file?

			}

			else {
				return FALSE;		//if neither NODE nor LINK on command line
			}

			Stack_Push(back_value);
			return TRUE;
		}

		else
			return FALSE;		//cannot compute BACK until Nperiods > Back_Steps
	}

//*******************End of Stack Commands************ RK	
	
	
	
    switch (p->lhsVar.attribute)
    {
    case r_TIME:
    case r_CLOCKTIME:
    case r_TIMEOPEN:                                                           //(5.1.010)
    case r_TIMECLOSED:                                                         //(5.1.010)
        return compareTimes(lhsValue, p->relation, rhsValue, tStep/2.0); 

    default:
        return compareValues(lhsValue, p->relation, rhsValue);
    }
}

//=============================================================================

double getVariableValue(struct TVariable v)
{
    int i = v.node;
    int j = v.link;

    switch ( v.attribute )
    {
      case r_TIME:
        return ElapsedTime;
        
      case r_DATE:
        return CurrentDate;

      case r_CLOCKTIME:
        return CurrentTime;

      case r_DAY:
        return datetime_dayOfWeek(CurrentDate);

      case r_MONTH:
        return datetime_monthOfYear(CurrentDate);

      case r_STATUS:
        if ( j < 0 ||
            (Link[j].type != CONDUIT && Link[j].type != PUMP) ) return MISSING;
        else return Link[j].setting;
        
      case r_SETTING:
        if ( j < 0 || (Link[j].type != ORIFICE && Link[j].type != WEIR) )
            return MISSING;
        else return Link[j].setting;

      case r_FLOW:
        if ( j < 0 ) return MISSING;
        else return Link[j].direction*Link[j].newFlow*UCF(FLOW);

      case r_DEPTH:
        if ( j >= 0 ) return Link[j].newDepth*UCF(LENGTH);
        else if ( i >= 0 )
            return Node[i].newDepth*UCF(LENGTH);
        else return MISSING;

      case r_HEAD:
        if ( i < 0 ) return MISSING;
        return (Node[i].newDepth + Node[i].invertElev) * UCF(LENGTH);

      case r_VOLUME:                                                           //(5.1.008)
        if ( i < 0 ) return MISSING;
        return (Node[i].newVolume * UCF(VOLUME));

      case r_INFLOW:
        if ( i < 0 ) return MISSING;
        else return Node[i].newLatFlow*UCF(FLOW);

////  This section added to release 5.1.010.  ////                             //(5.1.010)
      case r_TIMEOPEN:
          if ( j < 0 ) return MISSING;
          if ( Link[j].setting <= 0.0 ) return MISSING;
          return CurrentDate + CurrentTime - Link[j].timeLastSet;

      case r_TIMECLOSED:
          if ( j < 0 ) return MISSING;
          if ( Link[j].setting > 0.0 ) return MISSING;
          return CurrentDate + CurrentTime - Link[j].timeLastSet;


      default: return MISSING;
	}
}

//=============================================================================

int compareTimes(double lhsValue, int relation, double rhsValue, double halfStep)
//
//  Input:   lhsValue = date/time value on left hand side of relation
//           relation = relational operator code (see RuleRelation enumeration)
//           rhsValue = date/time value on right hand side of relation 
//           halfStep = 1/2 the current time step (days)
//  Output:  returns TRUE if time relation is satisfied
//  Purpose: evaluates the truth of a relation between two date/times.
//
{
    if ( relation == EQ )
    {
        if ( lhsValue >= rhsValue - halfStep
        &&   lhsValue < rhsValue + halfStep ) return TRUE;
        return FALSE;
    }
    else if ( relation == NE )
    {
        if ( lhsValue < rhsValue - halfStep
        ||   lhsValue >= rhsValue + halfStep ) return TRUE;
        return FALSE;
    }
    else return compareValues(lhsValue, relation, rhsValue);
}

//=============================================================================

int compareValues(double lhsValue, int relation, double rhsValue)
//  Input:   lhsValue = value on left hand side of relation
//           relation = relational operator code (see RuleRelation enumeration)
//           rhsValue = value on right hand side of relation 
//  Output:  returns TRUE if relation is satisfied
//  Purpose: evaluates the truth of a relation between two values.
{
    SetPoint = rhsValue;
    ControlValue = lhsValue;
    switch (relation)
    {
      case EQ: if ( lhsValue == rhsValue ) return TRUE; break;
      case NE: if ( lhsValue != rhsValue ) return TRUE; break;
      case LT: if ( lhsValue <  rhsValue ) return TRUE; break;
      case LE: if ( lhsValue <= rhsValue ) return TRUE; break;
      case GT: if ( lhsValue >  rhsValue ) return TRUE; break;
      case GE: if ( lhsValue >= rhsValue ) return TRUE; break;
    }

    return FALSE;
}



// Added checkValue back in because doesn't really fit with compare value operation. Better to keep separate ///RK 10-8-2015
int checkValue(struct TPremise* p, double x) 
//
//  Input:   p = control rule premise condition
//           x = value being compared to value in the condition
//  Output:  returns TRUE if condition is satisfied
//  Purpose: evaluates the truth of a condition involving a numerical comparison.  AND PERFORMS VARIOUS STACK FUNCTIONS		2014-09-02:EMNET
//
{
	double tempValue = 0.0;			//

	SetPoint = p->value;
	ControlValue = x;

	switch (p->relation)
	{
		// ********************************************************************************************************************************************************
		// ********************************************************************************************************************************************************
		// ********************************************************************************************************************************************************
		//2014-09-02:EMNET --- added all STACK COMMANDS:

	case Stack_Enter:
		//////if ((p->node == -1) && (p->link == -1))		//if no Node or Link, push the STACK VALUE from the premise
		if ((p->lhsVar.attribute == r_STACK_OPER) || (p->lhsVar.attribute == r_STACK_RESULT))	{			//use the VALUE from the premise
			Stack_Push(p->value);
		}
		else {
			Stack_Push(ControlValue);				//otherwise, use the current ControlValue for the specified NODE or LINK from the current step in the simulation
			if (ControlValue != 0.0)
				writecon("");		//breakpoint
		}
		return TRUE;
		break;

	case Stack_Pop:
		if (Stack_Index < 1) return FALSE;
		Stack_Pop_value();		//ignoring the returned value
		return TRUE;
		break;

	case Stack_Add:
		if (Stack_Index < 1) return FALSE;
		///////////2014-10-10: ------------------ Control_Stack[Stack_Index] += Stack_Pop_value();		//OPTIMIZED WRONG IN DLL!!!!  Stack_Index is changed inside Stack_Pop_Value()   2014-10-10
		tempValue = Stack_Pop_value();
		Control_Stack[Stack_Index] += tempValue;		//add TOP-of-STACK and proper operand.  Must do in 2 steps.  OPTIMIZER WAS KILLING US IN DLL PROJECT!!!!!!!!!
		return TRUE;
		break;

	case Stack_Subtract:
		if (Stack_Index < 1) return FALSE;
		///////////2014-10-10: ------------------ Control_Stack[Stack_Index] -= Stack_Pop_value();		//OPTIMIZED WRONG IN DLL!!!!  Stack_Index is changed inside Stack_Pop_Value()   2014-10-10
		tempValue = Stack_Pop_value();
		Control_Stack[Stack_Index] -= tempValue;		//subtract proper operand from TOP-of-STACK.  Must do in 2 steps.  OPTIMIZER WAS KILLING US IN DLL PROJECT!!!!!!!!!
		return TRUE;
		break;

	case Stack_Multiply:
		if (Stack_Index < 1) return FALSE;
		///////////2014-10-10: ------------------ Control_Stack[Stack_Index] *= Stack_Pop_value();		//multiply TOP-of-STACK by proper operand

		tempValue = Stack_Pop_value();
		Control_Stack[Stack_Index] *= tempValue;		//multiply TOP-of-STACK by proper operand.  Must do in 2 steps.  OPTIMIZER WAS KILLING US IN DLL PROJECT!!!!!!!!!
		return TRUE;
		break;

	case Stack_Divide:
		if (Stack_Index < 1) return FALSE;
		tempValue = Stack_Pop_value();			//DIVIDE was already set up to use tempValue, and it works fine even when OPTIMIZE FOR SIZE is turned on.
		if (tempValue != 0.0)
			Control_Stack[Stack_Index] /= tempValue;		//divide TOP-of-STACK by proper operand
		else if (Control_Stack[Stack_Index] != 0.0)
			Control_Stack[Stack_Index] = BIG_NUMBER;				//return a "big" number if divide by zero (but just leave Control_Stack[Stack_Index] = 0.0 if we see 0.0 / 0.0)
		return TRUE;
		break;

	case Stack_Expo:
		if (Stack_Index < 1) return FALSE;
		tempValue = Stack_Pop_value();
		Control_Stack[Stack_Index] = pow(Control_Stack[Stack_Index], tempValue);		//raise TOP-of-STACK to the "operand" power
		return TRUE;
		break;

		//do not use Stack_Pop_value() for UNARY operators.  We do NOT want to pop the stack!
	case Stack_Invert:
		if (Stack_Index < 0) return FALSE;
		if (Control_Stack[Stack_Index] != 0.0)
			Control_Stack[Stack_Index] = 1.0 / Control_Stack[Stack_Index];
		return TRUE;
		break;

	case Stack_ChangeSign:
		if (Stack_Index < 0) return FALSE;
		Control_Stack[Stack_Index] *= -1.00;
		return TRUE;
		break;

	case Stack_Swap:
		if (Stack_Index < 1) return FALSE;
		tempValue = Control_Stack[Stack_Index];
		Control_Stack[Stack_Index] = Control_Stack[Stack_Index - 1];
		Control_Stack[Stack_Index - 1] = tempValue;
		return TRUE;
		break;

	case Stack_LOG10:
		if (Stack_Index < 0) return FALSE;
		if (Control_Stack[Stack_Index] > 0.0)
			Control_Stack[Stack_Index] = log10(Control_Stack[Stack_Index]);
		else
			Control_Stack[Stack_Index] = 0.0;
		return TRUE;
		break;

	case Stack_LN:
		if (Stack_Index < 0) return FALSE;
		if (Control_Stack[Stack_Index] > 0.0)
			Control_Stack[Stack_Index] = log(Control_Stack[Stack_Index]);
		else
			Control_Stack[Stack_Index] = 0.0;
		return TRUE;
		break;

	case Stack_EXP:
		if (Stack_Index < 0) return FALSE;
		Control_Stack[Stack_Index] = exp(Control_Stack[Stack_Index]);
		return TRUE;
		break;

	case Stack_SQRT:
		if (Stack_Index < 0) return FALSE;
		if (Control_Stack[Stack_Index] > 0.0)
			Control_Stack[Stack_Index] = sqrt(Control_Stack[Stack_Index]);
		else
			Control_Stack[Stack_Index] = 0.0;
		return TRUE;
		break;

	case Stack_SIN:
		if (Stack_Index < 0) return FALSE;
		Control_Stack[Stack_Index] = sin(Control_Stack[Stack_Index]);			//input angle in RADIANS
		return TRUE;
		break;

	case Stack_COS:
		if (Stack_Index < 0) return FALSE;
		Control_Stack[Stack_Index] = cos(Control_Stack[Stack_Index]);			//input angle in RADIANS
		return TRUE;
		break;

	case Stack_TAN:
		if (Stack_Index < 0) return FALSE;
		Control_Stack[Stack_Index] = tan(Control_Stack[Stack_Index]);			//input angle in RADIANS
		return TRUE;
		break;

	case Stack_ASIN:
		if (Stack_Index < 0) return FALSE;
		if (fabs(Control_Stack[Stack_Index]) <= 1.0)
			Control_Stack[Stack_Index] = asin(Control_Stack[Stack_Index]);		//result angle in RADIANS
		else
			Control_Stack[Stack_Index] = BIG_NUMBER;
		return TRUE;
		break;

	case Stack_ACOS:
		if (Stack_Index < 0) return FALSE;
		if (fabs(Control_Stack[Stack_Index]) <= 1.0)
			Control_Stack[Stack_Index] = acos(Control_Stack[Stack_Index]);		//result angle in RADIANS
		else
			Control_Stack[Stack_Index] = BIG_NUMBER;
		return TRUE;
		break;

	case Stack_ATAN:
		if (Stack_Index < 0) return FALSE;
		Control_Stack[Stack_Index] = atan(Control_Stack[Stack_Index]);			//result angle in RADIANS
		return TRUE;
		break;


		//Stack comparison operators follow.  Return TRUE or FALSE based on comparison:


	case Stack_Equal:
		if (Stack_Index < 1) return FALSE;
		if (fabs(Control_Stack[Stack_Index] - Control_Stack[Stack_Index - 1]) <= EPSILON)
			return TRUE;		//if TOP-of-STACK is CLOSE ENOUGH TO EQUAL TO the next item on the stack
		else
			return FALSE;
		break;

	case Stack_NotEqual:
		if (Stack_Index < 1) return FALSE;
		if (fabs(Control_Stack[Stack_Index] - Control_Stack[Stack_Index - 1]) > EPSILON)
			return TRUE;		//if TOP-of-STACK is NOT CLOSE ENOUGH TO EQUAL TO the next item on the stack
		else
			return FALSE;
		break;

	case Stack_Greater:
		if (Stack_Index < 1) return FALSE;
		if (Control_Stack[Stack_Index] > Control_Stack[Stack_Index - 1])
			return TRUE;		//if TOP-of-STACK is GREATER THAN the next item on the stack
		else
			return FALSE;
		break;

	case Stack_GreaterEqual:
		if (Stack_Index < 1) return FALSE;
		if (Control_Stack[Stack_Index] >= Control_Stack[Stack_Index - 1])
			return TRUE;		//if TOP-of-STACK is GREATER THAN OR EQUAL TO the next item on the stack
		else
			return FALSE;
		break;


	case Stack_LessThan:
		if (Stack_Index < 1) return FALSE;
		if (Control_Stack[Stack_Index] < Control_Stack[Stack_Index - 1])
			return TRUE;		//if TOP-of-STACK is LESS THAN the next item on the stack
		else
			return FALSE;
		break;

	case Stack_LessThanEqual:
		if (Stack_Index < 1) return FALSE;
		if (Control_Stack[Stack_Index] <= Control_Stack[Stack_Index - 1])
			return TRUE;		//if TOP-of-STACK is LESS THAN OR EQUAL TO the next item on the stack
		else
			return FALSE;
		break;



		// ********************************************************************************************************************************************************
		// ********************************************************************************************************************************************************
		// ********************************************************************************************************************************************************


	}
	return FALSE;
}






void Stack_Push(double TopValue) {
	if (Stack_Index < MAX_STACK ) {
		Stack_Index++;
		Control_Stack[Stack_Index] = TopValue;
	}
	else {
		Stack_Index = Stack_Index;			//breakpoint
		//would return error ... but it's 1000 deep
	}

}

double Stack_Pop_value() {
	double temp;
	temp = Control_Stack[Stack_Index];
	if (Stack_Index > 0)  {
		Control_Stack[Stack_Index] = NAN;		//set unused stack entry to "undefined"
		Stack_Index--;
	}
	return temp;
}


void Clear_Stack() {
	int i;
	for (i = 0; i < MAX_STACK; i++) {
		Control_Stack[i] = NAN;
	}
	Stack_Index = -1;
}



//=============================================================================

void clearActionList(void)
//
//  Input:   none
//  Output:  none
//  Purpose: clears the list of actions to be executed.
//
{
    struct TActionList* listItem;
    listItem = ActionList;
    while ( listItem )
    {
        listItem->action = NULL;
        listItem = listItem->next;
    }
}

//=============================================================================

void  deleteActionList(void)
//
//  Input:   none
//  Output:  none
//  Purpose: frees the memory used to hold the list of actions to be executed.
//
{
    struct TActionList* listItem;
    struct TActionList* nextItem;
    listItem = ActionList;
    while ( listItem )
    {
        nextItem = listItem->next;
        free(listItem);
        listItem = nextItem;
    }
    ActionList = NULL;
}

//=============================================================================

void  deleteRules(void)
//
//  Input:   none
//  Output:  none
//  Purpose: frees the memory used for all of the control rules.
//
{
   struct TPremise* p;
   struct TPremise* pnext;
   struct TAction*  a;
   struct TAction*  anext;
   int r;
   for (r=0; r<RuleCount; r++)
   {
      p = Rules[r].firstPremise;
      while ( p )
      {
         pnext = p->next;
         free(p);
         p = pnext;
      }
      a = Rules[r].thenActions;
      while (a )
      {
         anext = a->next;
         free(a);
         a = anext;
      }
      a = Rules[r].elseActions;
      while (a )
      {
         anext = a->next;
         free(a);
         a = anext;
      }
   }
   FREE(Rules);
   RuleCount = 0;
}

//=============================================================================

// Added by Fred M. in 2014. - Emnet ///RK 
int  findExactMatch(char *s, char *keyword[])
//
//  Input:   s = character string
//           keyword = array of keyword strings
//  Output:  returns index of keyword which matches s or -1 if no match found  
//  Purpose: finds exact match between string and array of keyword strings.
//
{
   int i = 0;
   while (keyword[i] != NULL)
   {
      if ( strcomp(s, keyword[i]) ) 
		  return(i);
      i++;
   }
   return(-1);
}

//=============================================================================
