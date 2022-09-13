\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{urjc}[2022/09/13 URJC LaTeX class by Joaquín Arias]

\LoadClass[12pt, a4paper]{article}
\RequirePackage[left=3.5cm,top=2cm,right=3cm,includehead]{geometry}

%%%%%%%%%%%%%%%%%%%%%%% Estilo de bibliografia
\RequirePackage{csquotes}
\PassOptionsToPackage{
  natbib=true,
  style=bwl-FU,%	authoryear-comp,
  maxbibnames=99,
%  firstinits=true,
  firstinits=false,
  backend=bibtex,
}   {biblatex}
\RequirePackage{biblatex}
\DeclareNameAlias{sortname}{last-first} 

\DeclareCiteCommand{\cite}[\mkbibparens]
{\usebibmacro{prenote}}
{\usebibmacro{citeindex}%
  \printtext[bibhyperref]{\printnames[cite]{labelname} \printfield[cite]{year}}}%{\usebibmacro{cite}}}
{\multicitedelim}
{\usebibmacro{postnote}}
% Titles in bold
\DeclareFieldFormat*{title}{\textbf{#1}}
\DeclareCiteCommand{\citetitle}
{\usebibmacro{prenote}}
{\usebibmacro{citeindex}%
  \printtext[bibhyperref]{\printfield[cite]{labeltitle} (\printfield[cite]{year})}}
{\multicitedelim}
{\usebibmacro{postnote}}


%%%%%%%%%%%%%%%%%%%%%%% Estilo de enlaces

\RequirePackage[colorlinks=true,pdftex]{hyperref}
\hypersetup{
  linktocpage,
  bookmarksopen=true,
  bookmarksnumbered=true,
  breaklinks=true,
  hidelinks,
  pageanchor=true,
  colorlinks,
  linktocpage,
  citecolor=linkcolor,
  urlcolor=linkcolor,
  linkcolor=linkcolor
}
\renewcommand*{\UrlFont}{\ttfamily\small\relax}
    

%%%%%%%%%%%%%%%%%%%%%%% Paquetes (no modificar)
\RequirePackage[utf8]{inputenc}
\RequirePackage[spanish,es-lcroman,es-tabla]{babel}
\RequirePackage[T1]{fontenc}
\RequirePackage[pdftex]{graphicx}
\RequirePackage{mathtools}
\RequirePackage{mathptmx}
\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{enumitem}
\RequirePackage[justification=centering]{caption}
\setlength\abovecaptionskip{0.5em}
\setlength\belowcaptionskip{-0.25em}
 \RequirePackage[figuresright]{rotating}
 \RequirePackage{booktabs}
\RequirePackage{multirow}
\RequirePackage{xltabular}
\RequirePackage{longtable}
\RequirePackage{pdflscape}
\RequirePackage{afterpage}
\RequirePackage{relsize}
\RequirePackage{color}
\RequirePackage{xcolor}
\RequirePackage{booktabs}
\RequirePackage{subcaption}
\definecolor{linkcolor}{RGB}{52,59,144}
\definecolor{Comment}  {RGB}{169,082,044}
\definecolor{Bluedark} {RGB}{0,0,180}
\definecolor{Bluelight}{RGB}{070,100,250}
\definecolor{Browndark}{rgb}{0.2,0.2,0.2}
\definecolor{gray}{rgb}{0.6,0.6,0.6}
\RequirePackage{tikzpagenodes}

%%%%%%%%%%%%%%%%%%%%%%% Estilo de páginas
\RequirePackage{fancyhdr}
\pagestyle{fancy}
\fancyhf{}
\setlength{\headheight}{15.2pt}
%\renewcommand{\chaptermark}[1]{\markboth{\uppercase{#1}}{}}
\renewcommand*{\headrulewidth}{0pt}
\fancyhead[EL]{ \textsf{\relsize{-1}{\leftmark\ }} \hrulefill }
\fancyhead[OR]{ \hrulefill \textsf{\relsize{-1}{\ \nouppercase\rightmark} } }
\fancyfoot[C]{\thepage}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Portada
\renewcommand*{\maketitle}{%
\begin{titlepage}
  \pagestyle{plain}

  \begin{center}
    \vspace*{-4em}
    \includegraphics[scale=.3]{urjc-logo}\\
    \vspace*{2em}
    \textsc{\LARGE Escuela Técnica Superior\\de Ingeniería Informática}\\
    \vspace*{2em}
    \textsc{\Large \grado}\\  % Grado definido por el alumno
    \vspace*{\fill}
    \textbf{\LARGE \titulotrabajo\\}  % Titulo del TFG  definido por el alumno
    \vspace*{2em}
    \textsc{\large \asignatura\\}
    \vspace*{.5em}
    \textsc{\large \curso\\}  % Curso definido por el alumno
    \vspace*{4em}\vspace*{\fill}
    {%
      \large
      \begin{tabular}{rl}
        \textbf{Autores:} & \textbf{\autorone}\\
         & \textbf{\autortwo} \\
         & \textbf{\autorthree}
      \end{tabular}
    }
  \end{center}

  \vspace*{2em}

  \let\thefootnote\relax\footnotetext{
    \hspace*{-2em}
    \begin{tabular}[m]{p{.22\textwidth}p{.75\textwidth}}
      \hspace*{-1em}
      \includegraphics[width=.22\textwidth]{urjc-by-sa}
      &
        { \small \vspace*{-3em}
        Copyright (c) 2022 \autorone, \autortwo.
        % 
        Esta obra está bajo la licencia CC BY-SA 4.0,
        \href{https://creativecommons.org/licenses/by-sa/4.0/deed.es}{Creative Commons Atribuciónn-CompartirIgual 4.0 Internacional}.
        }
        
    \end{tabular}
    \vspace*{-8em}
  }

  
\end{titlepage}
}

