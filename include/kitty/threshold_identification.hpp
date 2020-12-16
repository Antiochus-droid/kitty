/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <stdio.h>
#include <stdlib.h>

/*ILP_SOLVE LIBRARY*/
#include <iostream>
#include <cstdlib>
#include <string>
#include <fstream>
#include <iostream>
#include <cassert>





#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */

/*Include SOP representation of tt*/
#include "isop.hpp"

#include "traits.hpp"
#include "operations.hpp"
#include "properties.hpp"
#include "implicant.hpp"
#include "print.hpp"
#include "cube.hpp"
#include "constructors.hpp"
#include "bit_operations.hpp"



namespace kitty {


    template<typename TT, typename = std::enable_if_t <is_complete_truth_table<TT>::value>>
//Negative Unate  verification variable function
     bool neg_unate(const TT &tt, int64_t i) {

        auto numvars = tt.num_vars();


        auto const tt1 = cofactor0(tt, i);
        auto const tt2 = cofactor1(tt, i);
        for (auto bit = 0; bit < (2 << (numvars - 1)); bit++) {
            if (get_bit(tt1, bit) >= get_bit(tt2, bit)) {
                continue;
            } else {
                return false;
            }
        }
        return true;

    }

    template<typename TT, typename = std::enable_if_t <is_complete_truth_table<TT>::value>>

    //Positive Unate verification variable function
     bool pos_unate(const TT &tt, int64_t i) {

        auto numvars = tt.num_vars();


        auto const tt1 = cofactor0(tt, i);
        auto const tt2 = cofactor1(tt, i);
        for (auto bit = 0; bit < (2 << (numvars - 1)); bit++) {
            if (get_bit(tt1, bit) <= get_bit(tt2, bit)) {
                continue;
            } else {
                return false;
            }
        }
        return true;

    }

    template<typename TT, typename = std::enable_if_t <is_complete_truth_table<TT>::value>>
    //Unate  function or not (each variable or positive or negative unate)
     bool unate(const TT &tt) {
        int numvars = tt.num_vars();
        for (int i = 0u; i < numvars; i++) {

            if (neg_unate(tt, i) == true || pos_unate(tt, i) == true) {
                continue;
            } else {
                return false;
            }
        }
        return true;
    }


    template<typename TT, typename = std::enable_if_t <is_complete_truth_table<TT>::value>>

    bool is_threshold(const TT &tt, std::vector <int64_t> *plf = nullptr) {

        std::vector <int64_t> linear_form;
        std::vector <int8_t> negative_unate;  //  In vector all the bits  which are negative unate
        TT tt1 = tt;

        //If not  unate  -->  not TF-function
        if (unate(tt) == false) {
             return false;
        }
        /*we do f' to have only a  positive  unate variable  function */
        for (unsigned int i = 0u; i < tt.num_vars(); i++) {

            if (pos_unate(tt, i) == true) {
                continue;
                /* If not positive unate it is negative and we flip  and  store to have only positive unate function
                 * f' */
            } else {
                negative_unate.push_back(i);
                flip_inplace(tt1, i);

            } /* allows to flip the index to obtain only positive unate on tt1*/
        }
        /* We calculate ONSET and  OFFSET  SOP notation with f' */
        std::vector <cube> cubes_pos = isop(tt1);
        std::vector <cube> cubes_neg = isop(unary_not(tt1));

        /* ILP SOLVE */


        lprec *lp;
        int Ncol, *colno = NULL, ret = 0;
        REAL *row = NULL;
        Ncol = tt.num_vars() + 1;

        /* We will build the model row by row */


        lp = make_lp(0, Ncol);
        if (lp == NULL) {
            return false; /* couldn't construct a new model... */}





        colno = (int *) malloc(Ncol * sizeof(*colno));
        row = (REAL *) malloc(Ncol * sizeof(*row));

        if ((colno == NULL) || (row == NULL)) {
            return false;
        }
        // All variables are positive (weights and Treshold)
         if (ret == 0) {
            set_add_rowmode(lp, TRUE);
            for (int i = 0; i < Ncol; i++) {

                for (int j = 0; j < Ncol; j++) {

                    colno[j] = j + 1;
                    if (i == j) {
                        row[j] = 1;
                    }

                    else{
                        row[j] = 0;
                    }
                }
                add_constraintex(lp, Ncol, row, colno, GE, 0);

            }
        }

        if (ret == 0) {

                //ONSET equations
            for (unsigned long c = 0; c < cubes_pos.size(); c++) {

                cube C = cubes_pos.at(c);

                for (uint8_t i = 0; i < tt.num_vars(); i++) {
                    colno[i] = i + 1;
                    bool mask = C.get_mask(i); //If  variable is in the cube

                    if (mask) {
                        row[i] = 1.0;
                    } else {
                        row[i] = 0.0;
                    }

                }
                colno[tt.num_vars()]=tt.num_vars()+1;
                row[tt.num_vars()] = -1.0;

                add_constraintex(lp, Ncol, row, colno, GE, 0);

            }
        }


            if (ret == 0) {
                //OFFSET equations
                for (unsigned long c = 0; c < cubes_neg.size(); c++) {

                    cube C = cubes_neg.at(c);
                    for (uint8_t i = 0; i < tt.num_vars(); i++) {
                        colno[i] = i + 1;


                        bool mask = C.get_mask(i); //If variable is not on the cube

                        if ( !mask) {
                            row[i] = 1.0;
                        } else {
                            row[i] = 0.0;
                        }
                    }
                    colno[tt.num_vars()] = tt.num_vars() + 1; //For  the treshold condition
                    row[tt.num_vars()] = -1.0;


                    add_constraintex(lp, Ncol, row, colno, LE, -1);

                }
            }

                if (ret == 0) {
                    set_add_rowmode(lp, FALSE); /* rowmode should be turned off again when done building the model */



                    for (int j = 0; j < Ncol; j++) {
                        colno[j] = j + 1;
                        row[j] = 1;
                    }


                    set_obj_fnex(lp, Ncol, row, colno);

                }


                    /* set the object direction to minimize */
                    set_minim(lp);

      //  write_LP(lp, stdout);
      //  write_lp(lp, "model.lp");



                    set_verbose(lp, IMPORTANT);

                    /* Now let lpsolve calculate a solution */
                    ret = solve(lp);
                   if (ret != 0){
                       if ( colno != NULL )
                           free( colno );
                       if ( row != NULL )
                           free( row );

                       if ( lp != NULL )
                           delete_lp( lp );
                        return false;
                    }



                else{


                    get_variables(lp, row);


                    //Linear_form make all variables
                    for (int i = 0; i < Ncol; i++) {
                        linear_form.push_back((int64_t) row[i]); //Int64_T to avoid issues
                    }

                    //Change from f"  to  f (redo negative unate variablesc condition)
                    for (auto i : negative_unate) {
                        linear_form.at(i) = -linear_form.at(i);
                        linear_form[Ncol - 1] = linear_form[Ncol - 1] + linear_form[i];
                    }



                    *plf = linear_form;
                    //Free space
                if ( colno != NULL )
                    free( colno );
                if ( row != NULL )
                    free( row );

                if ( lp != NULL )
                    delete_lp( lp );


                return true;
            }
        }

    }



/* namespace kitty */

