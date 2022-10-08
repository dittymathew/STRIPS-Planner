

import java.io.File;
import java.io.FileNotFoundException;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Properties;
import java.util.Set;

import org.paukov.combinatorics.Factory;
import org.paukov.combinatorics.Generator;
import org.paukov.combinatorics.ICombinatoricsVector;



import pddl4j.*;
import pddl4j.ErrorManager.Message;
import pddl4j.PDDLObject.Content;
import pddl4j.exp.AndExp;
import pddl4j.exp.AtomicFormula;
import pddl4j.exp.DerivedPredicate;
import pddl4j.exp.Exp;
import pddl4j.exp.InitEl;
import pddl4j.exp.NotAtomicFormula;
import pddl4j.exp.action.Action;
import pddl4j.exp.action.ActionDef;
import pddl4j.exp.term.Constant;
import pddl4j.exp.term.Substitution;
import pddl4j.exp.term.Term;
import pddl4j.exp.term.Variable;

public class strips {
 
    static ArrayList visit_goal =new ArrayList();
	public static void main(String[] args) throws FileNotFoundException {
	 
	    	 Properties options = new Properties();
	    	 options.put(RequireKey.STRIPS, true);
	    	 options.put(RequireKey.TYPING, true);
	    	 options.put(RequireKey.EQUALITY, true);
	    	 options.put(RequireKey.UNIVERSAL_PRECONDITIONS, true);
	    	 options.put(RequireKey.CONDITIONAL_EFFECTS, true);
	    	 options.put(RequireKey.NEGATIVE_PRECONDITIONS, true);
	    
	         // Creates an instance of the java pddl parser
	         Parser parser = new Parser(options);
	         Domain domain = parser.parse(new File("/home/ditty/workspace/strips/src/blocksworld.pddl"));
	         Problem problem = parser.parse(new File("/home/ditty/workspace/strips/src/pb4.pddl"));
	         PDDLObject obj = parser.link(domain, problem);
	         
	         
	         // Gets the error manager of the pddl parser
	         ErrorManager mgr = parser.getErrorManager();
	         
	         // If the parser produces errors we print it and stop
	         if (mgr.contains(Message.ERROR)) {
	             mgr.print(Message.ALL);
	         } // else we print the warnings
	         else {
	             mgr.print(Message.WARNING);
	             System.out.println("\nParsing domain \"" + domain.getDomainName()
	                         + "\" done successfully ...");
	             System.out.println("Parsing problem \"" + problem.getProblemName()
	                         + "\" done successfully ...\n");
	         }
	         //Initial state
	         List<InitEl> list =obj.getInit(); ///get initial state
	         System.out.println("Initial State");
	         System.out.println(list);
	         System.out.println("Goal");
	         System.out.println(Goal(obj));
	         ArrayList curstate = new ArrayList();
	         ArrayList s = new ArrayList();
	         curstate.addAll(list); ///store the initial state to curstate
	         ArrayList actions = new ArrayList(); 
	         Plan p;
	         int depth =100;
	       	 p=groundStrips(obj,curstate,Goal(obj),depth++,0); //Calling strips
	       	 s =stateTransition(curstate,p.getPlan(),p.getEff()); 
             if(s.containsAll(Goal(obj))){
	       	 System.out.println("Plan");
             
	         System.out.println(p.getPlan());
             }
             else {
            	 System.out.println("No Plan");
             }
	     }
	/*
	 * Function name : groundStrips
	 * Purpose		 : To do Strips algorithm
	 * Arguments	 : 	
	 * 					1) obj - PDDLObject
	 * 					2) s   - Current state
	 * 					3) g   - Goal
	 * Return 		 : Plan 
	 * 
	 */
	public static Plan groundStrips(PDDLObject obj,ArrayList s, ArrayList g,int depth,int level){
		
		ArrayList plan =new ArrayList();
		ArrayList relact =new ArrayList();
		ArrayList relprecond =new ArrayList();
		ArrayList releff =new ArrayList();
		RelActions rel =new RelActions();
		Plan p =new Plan(); // empty plan
		int i;
		
		
		while(true){
			if(s.containsAll(g)){ // if s satisfies g then return p
				p.end =2;
				return p;
			}
			
			rel =findRelActions(obj,g); //  get relevant actions for goal g 
			
			relact =rel.getActions(); // store relevant actions into arraylist relact
			relprecond = rel.getPre();// store relevant action's preconditions into arraylist relprecond
			releff = rel.getEff();// store relevant action's effect into arraylist releff
			
			if(relact.isEmpty()){ // if relact  is empty then return failure
				p.fail =true;
				return p;
			}
			for(i=0;i<relact.size();i++){ //Non deterministically choosing relevant action 
				
			
				Plan np;
				ArrayList newplan =new ArrayList();
				ArrayList effect =new ArrayList();
				
				if(checkRevisit((ArrayList)relprecond.get(i))){ //if not visited
					visit_goal.add(relprecond.get(i));
				
					np =groundStrips(obj,s,(ArrayList)relprecond.get(i),depth,level++); // recursively call groundStrips for preconditon of relevant action as goal
					if(np.end==1){
						return np;
					}
					newplan = np.getPlan();	
					plan=p.getPlan();
					effect =p.getEff();
					
					//if newplan(np) is not failure  means newplan achives precond(a) from s   
					if(np.fail ==false && np.end != 3){ //if np.end ==3 go to next action in the relevant actions
					
						s =stateTransition(s,newplan,np.getEff()); //applying the newplan to s
						s=getNextState(s,releff.get(i)); //applying the i th action 
						plan =append(plan,newplan,relact.get(i)); //appending plan
						effect = append(effect,np.getEff(),releff.get(i));
					
						p.setPlan(plan);
						p.setEff(effect);
						p.setEnd(2);
					
						break;
					}
				}
			}
			if(i==relact.size()){ 
				p.end=3;
				return p;
			}
			
			
		
		}
		
	
	}

	/*
	 * Function checkEquals
	 * 
	 * Arguments : state, newstate
	 * 
	 * Purpose	 : To check whether two states are equal
	 * 
	 * Return : true if equal
	 * 			false if not equal
	 * 
	 */
	public static boolean checkEquals(ArrayList state, ArrayList newstate){
		boolean k= false;
		int i,j,count;
		count =0;

		// if size is not equal return false
		if(state.size()!=newstate.size())
			return k;
		
		//checking
		for(i=0;i<state.size();i++){
			for(j=0;j<newstate.size();j++){
				if(state.get(i).equals(newstate.get(j))){
					count++; // setting count
					break;
				}
			}
		}
		
		//  if count is equal means states are equal, then return true
		if(count==state.size() && count==newstate.size()){
		
			return true;
		}
		return k;
	}
	/*
	 * Function to check revisiting
	 * Returns true if not visited
	 * 		   false if visited
	 */
	public static boolean checkRevisit(ArrayList state){
		boolean k =true;
		
		if(visit_goal.isEmpty())
			return k;
		int k6;
       	for(k6=0;k6<visit_goal.size();k6++){
       		if(checkEquals(state,(ArrayList) visit_goal.get(k6))){
       			k=false;
       			
       		}
        }
       	
       		
       	return k;
	}
	public static ArrayList stateTransition(ArrayList s, ArrayList newplan,ArrayList effect){
		int i;
		//ArrayList curState =new ArrayList();
		for(i=0;i<newplan.size();i++){
			s = getNextState(s,effect.get(i));
		}
		return s;
	}
	public static ArrayList append(ArrayList plan, ArrayList newplan, Object a){
		int i;
		ArrayList np =new ArrayList();
		np.addAll(plan);
		np.addAll(newplan);
		/*for(i=0;i<newplan.size();i++){
			plan.add(newplan.get(i));
		}*/
		np.add(a);
		return np;
	}
	/*
	 * Function to get next state give a state and and actions effects
	 */
	public static ArrayList getNextState(ArrayList state,Object effect){
		ArrayList newstate =new ArrayList();
		
		//effect= ap.getEffect();
		AndExp andExp = (AndExp) effect; ///get corres[ponding effects
    	ArrayList poseff = new ArrayList();
		ArrayList negeff = new ArrayList();
   	   	 Iterator<Exp> j = andExp.iterator();
       	 while(j.hasNext()){ ///for each predicates in the effect
       		 Object oj =j.next();
       		 if(oj.getClass().equals(AtomicFormula.class)) ///check for positive effects
       			poseff.add(oj); ///add to positive effect list
       		 else if(oj.getClass().equals(NotAtomicFormula.class)) ///check for negative effects
       		{
       			 NotAtomicFormula naf = (NotAtomicFormula)oj;
       			 negeff.add(naf.getExp()); /// add to negative effect list
       		
       		}
       	 }
       	 for(int k=0;k<state.size();k++){
       		newstate.add(state.get(k)); ///copying current state to newstate
       	 }
       	for(int k=0;k<negeff.size();k++){ ///removing negative effects from newstate
       		for(int ki=0;ki<state.size();ki++){
       			if(state.get(ki).equals(negeff.get(k))){
       				
       				newstate.remove(state.get(ki));
       				break;
       			}
       				
       		}
       	 }

       	for(int kj=0;kj<poseff.size();kj++){ ///Adding positive effects to newstate
       		int k3=0;
       		for(int ki=0;ki<state.size();ki++){
       			if(state.get(ki).equals(poseff.get(kj))){
       				k3=1;
       				break;
       			}
       		}
       		if(k3==0)
       			newstate.add(poseff.get(kj));
   			
   		}
       	return newstate;
	}
	/*
	 * fuction : Goal(obj)
	 * 
	 * Purpose : To return goal.
	 * 
	 */
	public static ArrayList Goal(PDDLObject obj){
        ArrayList goal = new ArrayList();
        Exp ex =obj.getGoal(); ///get goal state
  	   	 AndExp andExp = (AndExp) ex; ///goal state is type cast to AndExp
  	   	 
  	   	 Iterator<Exp> j = andExp.iterator(); //Iterating over predicates
      	 while(j.hasNext()){
      		Object oj =j.next();
      		goal.add(oj); ///adding goal predicates to arraylist goal
      	 }
      	 return goal;
	}
	
	/*
	 * Function : findRelActions(obj, g)
	 * 
	 * Purpose: To return relevant actions
	 * 
	 */
	public static RelActions findRelActions(PDDLObject obj,ArrayList g){
		int i;
        ArrayList constants = new ArrayList();
		Iterator<Constant> ic = obj.constantsIterator();
		while(ic.hasNext()) { ///storing constants to a list
			Object ob= ic.next();
			constants.add(ob);
		}
	
		RelActions rel =new RelActions();
		ArrayList rel_action =new ArrayList();
		ArrayList rel_precond =new ArrayList();
		ArrayList rel_eff =new ArrayList();
		//ArrayList rel_sub =new ArrayList();
		ArrayList actionlist =new ArrayList();
		ArrayList precondlist =new ArrayList();
		ArrayList efflist =new ArrayList();
		//ArrayList sublist =new ArrayList();
        Iterator <ActionDef> act = obj.actionsIterator();
        while(act.hasNext()) ///Iterating for each actions
        {
        	
        	ActionDef actionDef =act.next();
   	   		Action action = (Action)actionDef;
   	   		//System.out.println(action.getName() + "  "+ action.getParameters());
   	   		rel =checkRelevance(action,constants,g);
   	   		actionlist =rel.getActions();
   	   		precondlist = rel.getPre();
   	   		efflist = rel.getEff();
   	   		//sublist = rel.getSub();
   	   		if(!actionlist.isEmpty()){
   	   			for(i=0;i<actionlist.size();i++){
   	   				rel_action.add(actionlist.get(i));
   	   				rel_precond.add(precondlist.get(i));
   	   				rel_eff.add(efflist.get(i));
   	   		//		rel_sub.add(sublist.get(i));
   	   			}
   	   		}
   	   	
        }
          
        RelActions a=new RelActions();
	    a.setActions(rel_action);
	    a.setPre(rel_precond);
	    a.setEff(rel_eff);
	    //a.setSub(rel_sub);
	    
		return a;
	}
	
	public static boolean getConstantfromGoal(Substitution sigma, ArrayList g){
		int i;
		Substitution match =new Substitution();
		boolean k=true;
		for(i=0;i<g.size();i++){
			AtomicFormula gp = (AtomicFormula)g.get(i);
			AtomicFormula goal_predicate =new AtomicFormula(gp.getPredicate());
			match = gp.match(goal_predicate, sigma);
			if(match != sigma)
				k=false;
		}
		return true;
	}

	
	public static RelActions checkRelevance(Action action, ArrayList constants, ArrayList goal){
		boolean match;
		int parm_size =action.getParameters().size();
		ArrayList relgrndaction =new ArrayList();
		ArrayList relgrndpre =new ArrayList();
		ArrayList relgrndeff =new ArrayList();
		ArrayList relgrndsigma =new ArrayList();
		Set<Term> parm =action.getParameters();
		ArrayList<ArrayList<Constant>> constCombi = genComb(constants,parm_size);
		Iterator<ArrayList<Constant>> itrConst = constCombi.iterator();
		while(itrConst.hasNext()) {
			
			ArrayList<Constant> cons = itrConst.next();					
			Substitution sigma = new Substitution();
			Iterator itr2 = parm.iterator();
			Iterator itr3 = cons.iterator();
			while(itr2.hasNext()&&itr3.hasNext()) {				

				Variable var = (Variable) itr2.next();
				Constant constant = (Constant) itr3.next();
				sigma.bind(var, constant);
			}
			match =getConstantfromGoal(sigma,goal);
			if(match ==true){
			Exp exp_eff =action.getEffect();
			AtomicFormula name = new AtomicFormula(action.getName());
			for (Term p : action.getParameters()) {
				Term p_cnst =(Term)sigma.getBinding((Variable) p);
				if(p_cnst != null)
				name.add(p_cnst);
			
	          
			}
			
			//System.out.println(name);
		//	
			
			
			if (goalContainsEff(exp_eff.apply(sigma),goal)){
				//System.out.println(name);
				//System.out.println("Effect"+exp_eff.apply(sigma));
				//System.out.println("Goal check "+goal);
				relgrndpre.add(groundPrecondition(action,sigma));
				//relgrndsigma.add(sigma);
				relgrndaction.add(name);
				relgrndeff.add(exp_eff.apply(sigma));
			}
			}
		}
		RelActions a=new RelActions();
		    a.setActions(relgrndaction);
		    a.setPre(relgrndpre);
		    a.setEff(relgrndeff);
		   // a.setSub(relgrndsigma);
		    
			return a;
	}
	public static ArrayList groundPrecondition(Action action, Substitution sigma){
		ArrayList pre = new ArrayList();
		Exp exp = action.getPrecondition(); //get preconditions
        AndExp andExp = (AndExp) exp;
        Iterator<Exp> itr1 = andExp.iterator();
		while(itr1.hasNext()) {

			Exp pc = itr1.next();		
			pc = pc.apply(sigma); ///substituting variables in preconditions
			AtomicFormula af = (AtomicFormula) pc;
			pre.add(pc); ///store the substituted precondition 
		}
		return pre;
	}
	
	public static boolean goalContainsEff(Object effect, ArrayList goal){
		boolean flag;
		flag =false;
		AndExp andExp = (AndExp) effect; ///get corresponding effects
    	ArrayList poseff = new ArrayList();
		ArrayList negeff = new ArrayList();
   	   	 Iterator<Exp> j = andExp.iterator();
       	 while(j.hasNext()){ ///for each predicates in the effect
       		 Object oj =j.next();
       		 if(oj.getClass().equals(AtomicFormula.class)) ///check for positive effects
       			poseff.add(oj); ///add to positive effect list
       		 else if(oj.getClass().equals(NotAtomicFormula.class)) ///check for negative effects
       		{
       			 NotAtomicFormula naf = (NotAtomicFormula)oj;
       			 negeff.add(naf.getExp()); /// add to negative effect list
       		
       		}
       	 }
       	 int m,n;
		for(m=0;m<goal.size();m++){
			for(n=0;n<poseff.size();n++){
				if(goal.get(m).equals(poseff.get(n))){
					flag=true;
					break;
				}
			}
		}
		for(m=0;m<goal.size();m++){
			for(n=0;n<negeff.size();n++){
				if(goal.get(m).equals(negeff.get(n))){
					flag=false;
					break;
				}
			}
		}
		return flag;
	}
	public static ArrayList<ArrayList<Constant>> genComb(ArrayList constants, int noFreeVar) {

		ArrayList<ArrayList<Constant>> comb = new ArrayList<ArrayList<Constant>>();
		String fv[] = new String[constants.size()];
		for(int i=0,j=0;j<constants.size();i++,j++) {
			fv[i]=constants.get(j).toString();
		}
		ICombinatoricsVector<String> initialVector = Factory.createVector(fv);
		Generator<String> gen = Factory.createSimpleCombinationGenerator(initialVector, noFreeVar);

		for (ICombinatoricsVector<String> combination : gen) {

			java.util.List<String> l = combination.getVector();

			ICombinatoricsVector<String> temp = Factory.createVector(l);
			Generator<String> genPerm = Factory.createPermutationGenerator(temp);

			for (ICombinatoricsVector<String> perm : genPerm) {

				java.util.List<String> p = perm.getVector();
				ArrayList<Constant> c = new ArrayList<Constant>();
				Iterator<String> itr = p.iterator();
				while(itr.hasNext()) {
					c.add(new Constant(itr.next()));				
				}

				comb.add(c);
			}
		}	

		return comb;
	}

}
class RelActions{
	 	ArrayList  act_grounded ;
	    ArrayList pre_grounded ;
	    ArrayList effect_grounded ;
	    ArrayList sigma;
	   
	    public RelActions(){
	    	 act_grounded =new ArrayList();
	    	 pre_grounded =new ArrayList();
	    	 effect_grounded =new ArrayList();
	    	 sigma = new ArrayList();
	    }
	    public ArrayList getActions(){
	    	return this.act_grounded;
	    }
	    public ArrayList getPre(){
	    	return this.pre_grounded;
	    }
	    public ArrayList getEff(){
	    	return this.effect_grounded;
	    }
	    public ArrayList getSub(){
	    	return this.sigma;
	    }
	    public void setSub(ArrayList sigma){
	    	this.sigma =sigma;
	    }
	    public void setEff(ArrayList eff){
	    	this.effect_grounded =eff;
	    }
	    public void setActions(ArrayList act){
	    	this.act_grounded =act;
	    }
	    public void setPre(ArrayList precond){
	    	this.pre_grounded =precond;
	    }
}
class Plan{
	 boolean fail;
	 int end;
	ArrayList newplan ;
	ArrayList effect;
	public Plan(){
		newplan =new ArrayList();
		effect = new ArrayList();
		fail =false;
		end =0; // 1 : return and fail, 2 : return and success
	}
	public ArrayList getEff(){
    	return this.effect;
    }
	public ArrayList getPlan(){
    	return this.newplan;
    }
	public boolean getFail(){
    	return this.fail;
    }
	public int getEnd(){
    	return this.end;
    }
    public void setEnd(int end){
    	this.end =end;
    }
    public void setFail(boolean fail){
    	this.fail =fail;
    }
    public void setPlan(ArrayList plan){
    	this.newplan =plan;
    }
    public void setEff(ArrayList eff){
    	this.effect =eff;
    }
}