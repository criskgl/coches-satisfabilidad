import java.io.*;
import java.util.Scanner;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.utils.structures.IntVec;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
/*prueba commit*/

public class Coches {

	public static void main(String[] args) throws IOException {
		
		Store store = new Store();
		SatWrapper satWrapper = new SatWrapper(); 
		store.impose(satWrapper);					/* Importante: sat problem */
		
		String text = "";
		Scanner input = new Scanner(new File("src//input.dat"));
		
		System.out.println();	
		
		while(input.hasNext()) {
			 String i = input.next();
	         text += i;
		}
		
		int st = Character.getNumericValue(text.charAt(0)); //number of streets
		int pl = Character.getNumericValue(text.charAt(1)); //number of parking lots per street
		
		text = text.substring(2);
		
		System.out.println(text);

		//Matrices de VARIABLES
		BooleanVar isEmpty[][] = new BooleanVar[st][pl];
		BooleanVar catSup[][] = new BooleanVar[st][pl];
		BooleanVar catInf[][] = new BooleanVar[st][pl];
		BooleanVar catEq[][] = new BooleanVar[st][pl];
		//Matrices de LITERALES
		int[][] isEmptyLiteral = new int[st][pl];
		int[][] catSupLiteral = new int[st][pl];
		int[][] catInfLiteral = new int[st][pl];
		int[][] catEqLiteral = new int[st][pl];
		
		for(int i = 0; i<st; i++) {
			for(int j = 0; j<pl; j++) {
					isEmpty[i][j] = new BooleanVar(store, "La posicion "+j+" de la calle "+i+" esta: Vacia"); 
			
					/* Registramos las variables en el sat wrapper */
					satWrapper.register(isEmpty[i][j]);
					
					
				System.out.println(isEmpty[i][j]);
			}
		}
		
		
		
	
		for(int i = 0; i < st; i++) {
			for(int j = 0; j < pl; j++) {
					catSup[i][j] = new BooleanVar(store, "La categoria de la posicion "+j+" de la calle "+i+" SI es mayor que la posicion de la derecha"); 
					catInf[i][j] = new BooleanVar(store, "La categoria de la posicion "+j+" de la calle "+i+" SI es mayor que la posicion de la derecha"); 
					catEq[i][j] = new BooleanVar(store, "La categoria de la posicion "+j+" de la calle "+i+" SI es mayor que la posicion de la derecha"); 

					/* Registramos las variables en el sat wrapper */
					satWrapper.register(catSup[i][j]);
					satWrapper.register(catInf[i][j]);
					satWrapper.register(catEq[i][j]);
					
					
					
				System.out.println(catSup[i][j]);
				
			}
		}


		/* Todas las variables: es necesario para el SimpleSelect */
		//BooleanVar[] allVariables = new BooleanVar[]{x, y, z, w};


		/* Obtenemos los literales no negados de las variables 
		catSupLiteral[i][j] = satWrapper.cpVarToBoolVar(catSup[i][j], 1, true);
		catInfLiteral[i][j] = satWrapper.cpVarToBoolVar(catInf[i][j], 1, true);
		catEqLiteral[i][j] = satWrapper.cpVarToBoolVar(catEq[i][j], 1, true);
		*/
		

		/* Obtenemos los literales de todas las variables */
		int cont = 0;
 		
 		for(int i = 0; i<st; i++) {
 			for(int j = 0; j<pl; j++) {
 				if(text.charAt(cont) == '_')
 					isEmptyLiteral[i][j] = satWrapper.cpVarToBoolVar(isEmpty[i][j], 1, true);
 				else
 					isEmptyLiteral[i][j] = satWrapper.cpVarToBoolVar(isEmpty[i][j], 1, true); 
 				cont+=2;
 			}
 		}
 		
		cont = 0;
 		
 		for(int i = 0; i<st; i++) {
 			for(int j = 0; j<pl-1; j++) {
 				 				
 				if(text.charAt(cont) == '_'){
 					catSupLiteral[i][j] = satWrapper.cpVarToBoolVar(catSup[i][j], 0, false);
 					catInfLiteral[i][j] = satWrapper.cpVarToBoolVar(catInf[i][j], 0, false);
 					catEqLiteral[i][j] = satWrapper.cpVarToBoolVar(catEq[i][j], 0, false);
 				}
 				if(text.charAt(cont) > text.charAt(cont + 2)){
 					catSupLiteral[i][j] = satWrapper.cpVarToBoolVar(catSup[i][j], 1, false);
 					catInfLiteral[i][j] = satWrapper.cpVarToBoolVar(catInf[i][j], 0, false);
 					catEqLiteral[i][j] = satWrapper.cpVarToBoolVar(catEq[i][j], 0, false);
 				}
 				if(text.charAt(cont) < text.charAt(cont + 2)){
 					catSupLiteral[i][j] = satWrapper.cpVarToBoolVar(catSup[i][j], 0, false);
 					catInfLiteral[i][j] = satWrapper.cpVarToBoolVar(catInf[i][j], 1, false);
 					catEqLiteral[i][j] = satWrapper.cpVarToBoolVar(catEq[i][j], 0, false);
 				}
 				if(text.charAt(cont) == text.charAt(cont + 2)){
 					catSupLiteral[i][j] = satWrapper.cpVarToBoolVar(catSup[i][j], 0, false);
 					catInfLiteral[i][j] = satWrapper.cpVarToBoolVar(catInf[i][j], 0, false);
 					catEqLiteral[i][j] = satWrapper.cpVarToBoolVar(catEq[i][j], 1, false);
 				}
 				
 				
 				System.out.println("Sup: "+catSupLiteral[i][j]);
 				System.out.println("Inf: "+catInfLiteral[i][j]);
 				System.out.println("Equ: "+catEqLiteral[i][j]);
 				cont+=2;
 			}
 		}
 		System.out.println("");
 		 IntVar x = new IntVar(store, "X", 1,100);
 		System.out.println("PUTAMIERDA: "+x.dom().value());
 		 
 		for(int i = 0; i < st; i++){
 			for(int j = 0; j < pl-1; j++){
 				System.out.print("isEmpty: "+isEmpty[i][j].dom().value()+" ");
 			}
 			System.out.println("");
 		}
 			
		/* El problema se va a definir en forma CNF, por lo tanto, tenemos
		   que añadir una a una todas las clausulas del problema. Cada 
		   clausula será una disjunción de literales. Por ello, sólo
		   utilizamos los literales anteriormente obtenidos. Si fuese
		   necesario utilizar un literal negado, éste se indica con un
		   signo negativo delante. Ejemplo: -xLiteral */


//		/* Aristas */
//		/* Por cada arista una clausula de los literales involucrados */
//		addClause(satWrapper, xLiteral, yLiteral);		/* (x v y) */
//		addClause(satWrapper, xLiteral, zLiteral);		/* (x v z) */
//		addClause(satWrapper, yLiteral, zLiteral);		/* (y v z) */
//		addClause(satWrapper, yLiteral, wLiteral);		/* (y v w) */
//		addClause(satWrapper, zLiteral, wLiteral);		/* (z v w) */
//
//
//		/* Max agentes */
//		addClause(satWrapper, -xLiteral, -yLiteral, -zLiteral);		/* (-x v -y v -z) */
//		addClause(satWrapper, -xLiteral, -yLiteral, -wLiteral);		/* (-x v -y v -w) */
//		addClause(satWrapper, -xLiteral, -zLiteral, -wLiteral);		/* (-x v -z v -w) */
//		addClause(satWrapper, -yLiteral, -zLiteral, -wLiteral);		/* (-y v -z v -w) */
//
//
//		/* Resolvemos el problema */
//	    Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
//		SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariables,
//							 new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
//		Boolean result = search.labeling(store, select);
//
//		if (result) {
//			System.out.println("Solution: ");
//
//			if(x.dom().value() == 1){
//				System.out.println(x.id());
//			}
//
//			if(y.dom().value() == 1){
//				System.out.println(y.id());
//			}
//
//			if(z.dom().value() == 1){
//				System.out.println(z.id());
//			}
//
//			if(w.dom().value() == 1){
//				System.out.println(w.id());
//			}
//
//		} else{
//			System.out.println("*** No");
//		}
//
//		System.out.println();
	}


	public static void addClause(SatWrapper satWrapper, int literal1, int literal2){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		satWrapper.addModelClause(clause.toArray());
	}


	public static void addClause(SatWrapper satWrapper, int literal1, int literal2, int literal3){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		clause.add(literal3);
		satWrapper.addModelClause(clause.toArray());
	}
}
