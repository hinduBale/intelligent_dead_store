text <- paste("foo3 <- function(b)",
"{",
  "f <- 78",
  "x <- 59049",
  "res1 <- log10(x)",
  "rnorm(res1)",
  "x <- 654",
  "f <- 653", #This should be removed,since it is immediately being re-assigned ####  653  ####
  "f <- x", #This is also being removed, since f is not being called up ahead ####  x ####
  "res2 <- x^0.6",
  "return (c(res1, res2))",
"}",
sep = "\n"
)


fpd <- parse_text(text)
fpd <- flatten_leaves(fpd)

#Identifying functions and collecting their IDs, since dead store elimination happens only inside functions.
fun_ids <- fpd$id[fpd$token == "FUNCTION"]      #ID of the function
fun_prnt_ids <- fpd$parent[fpd$id %in% fun_ids] #ID of function parent


# get the expression of the function
id <- fun_prnt_ids
expr_id <- rev(fpd$id[fpd$parent == id & fpd$token %in% c("expr", "SYMBOL", constants)])[[1]]


list_of_exprs <- fpd[fpd$parent == expr_id & fpd$token == "expr", ]$id


#Declaring all variables
var_details <- NULL #var_details should be initialised outside the for loop.
remove_var_id <- NULL #remove_var_id should be initialised outside the for loop.

for(sid in list_of_exprs)
{
  exam_pd <- get_children(fpd, sid, TRUE) #This will also cover the cases where some_var <- c(2,54,var1, var2)                                          
  assign_type <- exam_pd[exam_pd$token %in% assigns & !exam_pd$text %in% c("<<-", "->>", ":="),"token"]
  ifelse(length(assign_type) > 0, assign_expr_flag <- TRUE, assign_expr_flag <- FALSE)
  if(assign_expr_flag == TRUE)
  {
    if(assign_type == "LEFT_ASSIGN" | assign_type == "EQ_ASSIGN")
    {
      assign_pid <- exam_pd[exam_pd$token %in% assigns & !exam_pd$text %in% c("<<-", "->>", ":="), "pos_id"]
      assigned_var <- exam_pd[exam_pd$token == "SYMBOL" & exam_pd$pos_id < assign_pid, "text"]
      called_var <- exam_pd[exam_pd$token == "SYMBOL" & exam_pd$pos_id > assign_pid, "text"]
    }
    else
    {
      assign_pid <- exam_pd[exam_pd$token %in% assigns & !exam_pd$text %in% c("<<-", "->>", ":="),"pos_id"]
      called_var <- exam_pd[exam_pd$token == "SYMBOL" & exam_pd$pos_id < assign_pid, "text"]
      assigned_var <- exam_pd[exam_pd$token == "SYMBOL" & exam_pd$pos_id > assign_pid, "text"]
    }
  }
  else #The case where no assignment takes place, for example rnorm(x)
  {
    called_var <- exam_pd[exam_pd$token == "SYMBOL", "text"]
  }
  
  ifelse(length(assigned_var) > 0, ifelse(assigned_var %in% var_details, assigned_flag <- TRUE, assigned_flag <- FALSE), assigned_flag <- NULL)
  ifelse(length(called_var) > 0, ifelse(called_var %in% var_details, called_flag <- TRUE, called_flag <- FALSE), called_flag <- FALSE)    #Actually it is impossible for a variable to have called_flag == FALSE, unless ofcourse that variable has been passed as a parameter.


  
  #We will evaluate called_var first to counter cases such as x <- 10; x <- log10(x); bla bla bla....
  if(!is.null(called_flag))
  {
    if(called_flag == FALSE)
    {
      var_details <- append(var_details, c(list_of_exprs[sid], called_var, TRUE))
    }
    #This is the case, that should be de-facto, where the called var is already in the var_details vector
    else
    {
      var_idx <- which(var_details == called_var)
      flag_idx <- var_idx + 1
      var_details[flag_idx] = TRUE
    }
  }
  
  #Now we will evaluate the assigned_var in the var_details list
  if(!is.null(assigned_flag))
  {
    #Now we have to make changes in the vector var_details
    if(assigned_flag == FALSE) #The case when the concerned variable is not in the var_detail vector
    {
      var_details <- append(var_details, c(sid, assigned_var, FALSE))
    }
    else #Case where the assigned variable is already present in the var_detail vector and it needs to be checked whether it has been called after its last assignment or not
    {
      var_idx <- which(var_details == assigned_var)
      flag_idx <- var_idx + 1
      pos_idx <- var_idx - 1
      if(var_details[flag_idx] == TRUE)  #This implies the situation where the var has been called after its assignment
      { 
        var_details[flag_idx] = FALSE
      }
      else #This implies the situation that the variable has not been called after its assignment
      { 
        #delete the earlier instance of the variable in question. For now, we will just store the IDs of the variables to be deleted
        remove_var_id <- append(remove_var_id, exam_pd[1, "id"])
        #now edit the pos_idx of the variable in the var_detail vector
        var_details[pos_idx] = sid
      }
    }
  }
}

#The main goal of this script was to obtain the remove_var_id vector.
remove_var_id

remove_nodes_from_id <- function(id_vec)
{
  for (vid in id_vec)
  {
    if (!vid %in% fpd$id)
    {
      next
    }
    a_fpd <- get_children(fpd, vid)
    na_fpd <- a_fpd
    a_prnt <- a_fpd[a_fpd$id == vid, ]
    a_sblngs <- a_fpd[a_fpd$parent == vid, ]
    
    # keep only the expression
    k_fpd <- a_sblngs[3, ]
    if (a_sblngs$token[[2]] == "RIGHT_ASSIGN")
    {
      k_fpd <- act_sblngs[1, ]
    }
    # remove assignment parent expr and siblings
    na_fpd <- na_fpd[!na_fpd$id %in% c(vid, a_sblngs$id), ]
    na_fpd <- rbind(na_fpd, k_fpd)
    
    # the expr to keep will skip the assignment expr in the fpd
    na_fpd[na_fpd$id == k_fpd$id, "parent"] <- a_prnt$parent
    
    # some fixes on the resulting fpd
    na_fpd <- na_fpd[order(na_fpd$pos_id), ]
    na_fpd[, c("next_spaces", "next_lines", "prev_spaces")] <- replace_pd(a_fpd, na_fpd)[ , c("next_spaces", "next_lines", "prev_spaces")]
    fpd <- rbind(remove_nodes(fpd, vid), na_fpd)
    fpd <- fpd[order(fpd$pos_id), ]
  }
  return (fpd)
}

#Now, the required fpd is given by
remove_nodes_from_id(remove_var_id)

#And, the deparsed data is given by
deparse_data(remove_nodes_from_id(remove_var_id))


